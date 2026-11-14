using System;
using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>Specifications: an expression of a contract, an assertion or an invariant, as mathematics (Spec's members, quantifiers, old).</summary>
    internal sealed partial class Lowering
    {
        // ------------------------------------------------------------------ specifications (mathematical)

        /// <summary>A specification: mathematics, its array reads, lengths, divisions and functions' calls kept for Checks' well-definedness.</summary>
        private KExpr Spec(IOperation e, IParameterSymbol result)
        {
            // (ObjSet.Empty: no objects)
            if ((e is IFieldReferenceOperation { Field.Name: "Empty", Instance: null } || e is IPropertyReferenceOperation { Property.Name: "Empty", Instance: null }) && IsObjSet(e.Type))
                return new KLit("(lambda r$: Ref :: false)");
            // (a slice a list pattern binds in a specification, .. var rest: its Length, and its elements, rest[i] a[start + i],
            // where 0 <= i < Length; nothing else of it)
            if (e is IPropertyReferenceOperation { Property.Name: "Length", Instance: ILocalReferenceOperation sll } && _bound.TryGetValue(sll.Local, out var slv) && slv is KOp { Op: "$slice" } slo)
                return slo.Args[2];
            if (e is IArrayElementReferenceOperation { ArrayReference: ILocalReferenceOperation sle, Indices.Length: 1 } sae && _bound.TryGetValue(sle.Local, out var sev) && sev is KOp { Op: "$slice" } seo)
            {
                var i = Spec(sae.Indices[0], result);
                var elem = new KElem { Array = seo.Args[0], Index = new KOp("+", seo.Args[1], i), ArrayType = sle.Local.Type, InSpec = true, At = sae.Syntax, ArrayAt = sae.Syntax };
                return new KOp("$need", new KOp("&&", new KOp("<=", new KLit("0"), i), new KOp("<", i, seo.Args[2])), elem);
            }
            if (e is ILocalReferenceOperation bl && _bound.TryGetValue(bl.Local, out var bv))
                return bv is KOp { Op: "$slice" } ? throw new NotTranslated("a slice in a specification, other than its Length and elements") : bv;
            // (a group a query's selector is given: its key, its count, Lowering.Linq's GroupValue)
            if (GroupValue(e) is KExpr group) return group;
            // (anonymous objects compared as objects, ==: their references, which the kernel's values (one per contents)
            // don't have: some relation, not known; != its negation)
            if (e is IBinaryOperation ao && ao.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals && AnonymousAsObject(ao.LeftOperand) && AnonymousAsObject(ao.RightOperand))
            {
                var eqv = new KOp("$refEq", Spec(Unconverted(ao.LeftOperand), result), Spec(Unconverted(ao.RightOperand), result));
                return ao.OperatorKind == BinaryOperatorKind.Equals ? eqv : new KOp("!", eqv);
            }
            if (DataExpr(e, x => Spec(x, result), (l, v) => _bound[l] = v, inSpec: true) is KExpr data) return data;
            // (a static readonly field the kernel doesn't have: its value, a constant of the run's, as in code)
            if (e is IFieldReferenceOperation { Field: { IsStatic: true, IsReadOnly: true } sro } && StaticReadonly(sro) is KExpr srov) return srov;
            // (a constant: its value; neither a delegate nor a lambda, the cases before it, is one)
            if (e.ConstantValue is { HasValue: true } cv && (Scalar(e.Type) || IsFloating(e.Type) || IsNullable(e.Type))) return Constant(cv.Value, e.Type);
            switch (e)
            {
                case IDelegateCreationOperation: return SpecOfDelegateCreation(e, result);
                case IAnonymousFunctionOperation: return SpecOfAnonymousFunction(e, result);
                case IParameterReferenceOperation: return SpecOfParameterReference(e, result);
                case ILocalReferenceOperation: return SpecOfLocalReference(e, result);
                case IInstanceReferenceOperation: return SpecOfInstanceReference(e, result);
                case IPropertyReferenceOperation: return SpecOfPropertyReference(e, result);
                case IFieldReferenceOperation: return SpecOfFieldReference(e, result);
                case IParenthesizedOperation: return SpecOfParenthesized(e, result);
                case IConversionOperation: return SpecOfConversion(e, result);
                case IUnaryOperation: return SpecOfUnary(e, result);
                case IConditionalOperation: return SpecOfConditional(e, result);
                case IBinaryOperation: return SpecOfBinary(e, result);
                case IArrayElementReferenceOperation: return SpecOfArrayElementReference(e, result);
                case IInvocationOperation: return SpecOfInvocation(e, result);
                case ICoalesceOperation: return SpecOfCoalesce(e, result);
                case IConditionalAccessOperation: return SpecOfConditionalAccess(e, result);
                case IConditionalAccessInstanceOperation: return SpecOfConditionalAccessInstance(e, result);
                default: return SpecOther(e, result);
            }
        }

        /// <summary>Spec of a delegate creation: its forms, in order; any other as SpecOther.</summary>
        private KExpr SpecOfDelegateCreation(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                case IDelegateCreationOperation d: return Spec(d.Target, result);
                default: return SpecOther(e, result);
            }
        }

        /// <summary>Spec of a anonymous function: its forms, in order; any other as SpecOther.</summary>
        private KExpr SpecOfAnonymousFunction(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                case IAnonymousFunctionOperation fn when fn.Body.Operations.Length == 1 && fn.Body.Operations[0] is IReturnOperation ret:
                    return Spec(ret.ReturnedValue, fn.Symbol.Parameters.FirstOrDefault() ?? result);
                default: return SpecOther(e, result);
            }
        }

        /// <summary>Spec of a parameter reference: its forms, in order; any other as SpecOther.</summary>
        private KExpr SpecOfParameterReference(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                case IParameterReferenceOperation p when result != null && SymbolEqualityComparer.Default.Equals(p.Parameter, result): return new KVar("result");
                case IParameterReferenceOperation cp when _capturedIn.ContainsKey(cp.Parameter): return CapturedInSpec(cp.Parameter);
                case IParameterReferenceOperation p when p.Parameter.ContainingSymbol is IMethodSymbol { MethodKind: MethodKind.AnonymousFunction } &&
                                                         !SymbolEqualityComparer.Default.Equals(p.Parameter.ContainingSymbol, _m):
                    return new KVar("q$" + p.Parameter.Name); // (a quantifier's variable)
                // (a base's contract, inherited: its parameters are this method's, by position)
                case IParameterReferenceOperation p when InSubset(p.Parameter.Type) && !_contract.IsStub && p.Parameter.ContainingSymbol is IMethodSymbol pm &&
                                                         _contract.Aliases.Any(a => SymbolEqualityComparer.Default.Equals(a.OriginalDefinition, pm.OriginalDefinition)) &&
                                                         p.Parameter.Ordinal < _m.Parameters.Length:
                    return new KVar(Local(_m.Parameters[p.Parameter.Ordinal]));
                // (a list member's stub: its @this is the receiver, the rest the member's own parameters)
                case IParameterReferenceOperation p when _contract.IsStub && (IsCollection(_m.ContainingType) || LibraryStub(_m)) && _contract.Stub != null &&
                                                         SymbolEqualityComparer.Default.Equals(p.Parameter.ContainingSymbol.OriginalDefinition, _contract.Stub.OriginalDefinition):
                    return SpecStubParameter(p);
                // (one it assigns: its variable; as it was on entry, in Spec.Old, the parameter itself)
                case IParameterReferenceOperation ap when _assigned.TryGetValue(ap.Parameter, out var apLocal):
                    return new KVar(_inOld > 0 && !_capturedParams.Contains(ap.Parameter) ? Local(ap.Parameter) : apLocal);
                // (a compiled query's lambda's, where it's called: its argument)
                case IParameterReferenceOperation cq when _compiledParams.Contains(cq.Parameter): return new KVar("q$" + cq.Parameter.Name);
                case IParameterReferenceOperation p when InSubset(p.Parameter.Type): return new KVar(Local(p.Parameter));
                default: return SpecOther(e, result);
            }
        }

        /// <summary>Spec of a local reference: its forms, in order; any other as SpecOther.</summary>
        private KExpr SpecOfLocalReference(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                case ILocalReferenceOperation cl when _capturedIn.ContainsKey(cl.Local): return CapturedInSpec(cl.Local);
                case ILocalReferenceOperation sr when _refAlias.TryGetValue(sr.Local, out var sra):
                    return sra.Var != null ? new KVar(sra.Var)
                         : new KElem { Array = sra.Array, Index = sra.Index, ArrayType = sra.ArrayType, InSpec = true, At = sr.Syntax, ArrayAt = sr.Syntax };
                case ILocalReferenceOperation l when InSubset(l.Local.Type): return new KVar(Declare(Local(l.Local), l.Local.Type));
                default: return SpecOther(e, result);
            }
        }

        /// <summary>Spec of a instance reference: its forms, in order; any other as SpecOther.</summary>
        private KExpr SpecOfInstanceReference(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                case IInstanceReferenceOperation { ReferenceKind: InstanceReferenceKind.ContainingTypeInstance }: return new KVar("this");
                default: return SpecOther(e, result);
            }
        }

        /// <summary>Spec of a property reference: its forms, in order; any other as SpecOther.</summary>
        private KExpr SpecOfPropertyReference(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                // (a view's object: v.Obj.Value)
                case IPropertyReferenceOperation { Property.Name: "Value", Instance: IPropertyReferenceOperation { Property.Name: "Obj" } obj } when IsView(obj.Instance?.Type) || IsShare(obj.Instance?.Type):
                    return Spec(obj.Instance, result);
                // (a [Pure] computed property: its getter, a function; in a contract class, the member it specifies)
                case IPropertyReferenceOperation cp when Specified(cp.Property) is IPropertySymbol sp && IsComputed(sp) && sp.GetMethod != null && _isFunction(sp.GetMethod):
                    return new KFnCall
                    {
                        Callee = OnThis(Specified(cp.Property).GetMethod, cp.Instance), Receiver = cp.Instance == null ? null : Spec(cp.Instance, result),
                        ReceiverIsThis = cp.Instance is IInstanceReferenceOperation, ReceiverAt = cp.Instance?.Syntax,
                        Args = cp.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => Spec(a.Value, result)).ToArray(), At = cp.Syntax,
                    };
                case IPropertyReferenceOperation pf when !(IsComputed(pf.Property) && !IsField(pf.Property.OriginalDefinition) && !_isFunction(pf.Property.GetMethod)) && !LibraryProperty(pf) && !(pf.Property.Name == "Length" && IsArray(ActualArray(pf.Instance?.Type))) && !IsString(pf.Instance?.Type) && CollectionOf(pf.Instance?.Type) == null && !IsPair(pf.Instance?.Type) && !SpecSymbols.IsCsVerifyType(pf.Instance?.Type, "Seq`1") &&
                                                      !SpecSymbols.IsCsVerifyType(pf.Instance?.Type, "Ghost`1") && !SpecSymbols.IsCsVerifyType(pf.Instance?.Type, "Map`2") && !IsCollectionInterface(pf.Property.ContainingType) && !IsMemValue(pf.Instance?.Type) && !IsGivenTask(pf.Instance?.Type):
                {
                    var (field, instance, onThis, instanceAt) = FieldOf(e, result, spec: true);
                    return Unbox(new KField { Field = field, Instance = instance, OnThis = onThis, At = e.Syntax, InstanceAt = instanceAt }, FieldType(field), e.Type);
                }
                case IPropertyReferenceOperation sl when sl.Property.Name == "Length" && IsString(sl.Instance?.Type):
                    return new KLen { String = true, Array = Spec(sl.Instance, result), InSpec = true, At = sl.Syntax, ArrayAt = sl.Instance.Syntax };
                case IPropertyReferenceOperation sc when sc.Property.IsIndexer && IsString(sc.Instance?.Type) && sc.Arguments.Length == 1:
                    return new KElem { String = true, Array = Spec(sc.Instance, result), Index = Spec(sc.Arguments[0].Value, result), InSpec = true, At = sc.Syntax, ArrayAt = sc.Instance.Syntax };
                // (a [Pure] indexer of a collection the models don't index, a StringBuilder's: its getter, as above)
                case IPropertyReferenceOperation pi when pi.Property.IsIndexer && pi.Instance != null && pi.Property.GetMethod != null && !(CollectionKind(pi.Instance.Type) is "List" or "Dictionary") &&
                                                         CollectionFunction(pi.Property.GetMethod) is IMethodSymbol gm:
                    return SpecIndexer(pi, gm, result);
                case IPropertyReferenceOperation pr when pr.Property.Name == "Length" && IsArray(ActualArray(pr.Instance?.Type)):
                    return new KLen { Array = Spec(pr.Instance, result), InSpec = true, At = pr.Syntax, ArrayAt = pr.Instance.Syntax };
                case IPropertyReferenceOperation lc when (lc.Property.Name == "Count" || lc.Property.Name == "Length" && CollectionKind(lc.Instance?.Type) == "StringBuilder") && CollectionOf(lc.Instance?.Type) is INamedTypeSymbol cc:
                    return Model("Size", cc, Spec(lc.Instance, result));
                // (a started task's Result, in a specification: what it gave (its join, and that it has finished, are code's))
                case IPropertyReferenceOperation { Property.Name: "Result", Instance: ILocalReferenceOperation srl } when _tasks.TryGetValue(srl.Local, out var srt) && srt.Result != null:
                    return new KVar(srt.Result);
                case IPropertyReferenceOperation sr when sr.Instance != null && IsCollectionInterface(sr.Property.ContainingType) &&
                                                         (sr.Property.Name == "Count" && sr.Arguments.Length == 0 || sr.Property.IsIndexer && sr.Arguments.Length == 1):
                    return Ifc(sr, sr.Property.IsIndexer ? Spec(sr.Arguments[0].Value, result) : null, Spec(sr.Instance, result), inSpec: true);
                case IPropertyReferenceOperation { Property.Name: "Count", Instance: IPropertyReferenceOperation { Property.Name: "Keys" or "Values", Instance: { } sd } } when CollectionOf(sd.Type) is INamedTypeSymbol sdc && CollectionKind(sdc) == "Dictionary":
                    return Model("Size", sdc, Spec(sd, result));
                case IPropertyReferenceOperation li when li.Property.IsIndexer && CollectionOf(li.Instance?.Type) is INamedTypeSymbol ic && li.Arguments.Length == 1 &&
                                                         CollectionKind(ic) is "List" or "Dictionary":
                    return SpecCollectionIndexer(li, ic, result);
                case IPropertyReferenceOperation sk when IsPair(sk.Instance?.Type) && sk.Property.Name is "Key" or "Value":
                    return Pair(Spec(sk.Instance, result), sk.Instance.Type, sk.Property.Name);
                // (a ghost map: a Boogie map; a ghost value's Value: the value)
                case IPropertyReferenceOperation mi when mi.Property.IsIndexer && SpecSymbols.IsCsVerifyType(mi.Instance?.Type, "Map`2") && mi.Arguments.Length == 1:
                    return new KOp("sel", Spec(mi.Instance, result), Spec(mi.Arguments[0].Value, result));
                case IPropertyReferenceOperation gv when gv.Property.Name == "Value" && SpecSymbols.IsCsVerifyType(gv.Instance?.Type, "Ghost`1"):
                    return Spec(gv.Instance, result);
                // (a ghost sequence: an [int] map; a ghost value: the value)
                case IPropertyReferenceOperation si when si.Property.IsIndexer && SpecSymbols.IsCsVerifyType(si.Instance?.Type, "Seq`1") && si.Arguments.Length == 1:
                    return new KOp("sel", Spec(si.Instance, result), Spec(si.Arguments[0].Value, result));
                case IPropertyReferenceOperation { Property.Name: "Empty", Instance: null } be when SpecSymbols.IsBag(be.Type):
                    return new KLit("$bag.empty");
                // (ghost sets of objects)
                case IPropertyReferenceOperation { Property.Name: "Empty" } empty when IsObjSet(empty.Type) && empty.Instance == null:
                    return new KLit("(lambda r$: Ref :: false)");
                case IPropertyReferenceOperation sct when sct.Instance != null && IsToken(sct.Instance.Type) && sct.Property.Name == "CanBeCanceled":
                    return new KOp("$canBeCanceled", Spec(sct.Instance, result));
                // (a library property that may change, in an assertion of the body's: not supported, CSV1901)
                // (in any of the method's own specifications:, not supported, CSV1901)
                case IPropertyReferenceOperation slp when _p.Result != null && LibraryProperty(slp) && !(slp.Instance != null && IsToken(slp.Instance.Type) && slp.Property.Name == "CanBeCanceled"):
                    return SpecLibraryProperty(slp);
                // (a computed property that isn't [Pure], read in an assertion of the body's: unknown, a warning)
                case IPropertyReferenceOperation npr when _p.Result != null && IsComputed(npr.Property) && npr.Property.GetMethod is IMethodSymbol ng && !_isFunction(ng) &&
                                                          !SpecSymbols.IsPure(npr.Property) && !(_contractOf?.Invoke(ng.OriginalDefinition) is Contract pc && pc.IsPure) && InSubset(npr.Type) &&
                                                          npr.Syntax.Ancestors().OfType<InvocationExpressionSyntax>().FirstOrDefault(i => i.Expression.ToString() is "Spec.Assert" or "Spec.Assume") != null:
                    return SpecImpureProperty(npr);
                default: return SpecOther(e, result);
            }
        }

        private KExpr SpecIndexer(IPropertyReferenceOperation pi, IMethodSymbol gm, IParameterSymbol result)
        {
            foreach (var model in Checks.StubModels(gm, _contractOf?.Invoke(gm))) _p.Models[model.Name] = model;
            _p.Stubs.Add(gm);
            var args = pi.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => Spec(a.Value, result)).ToArray();
            return new KFnCall { Callee = gm, Receiver = Spec(pi.Instance, result), ReceiverAt = pi.Instance.Syntax, Args = args, At = pi.Syntax, Stub = true };
        }

        /// <summary>Spec of a field reference: its forms, in order; any other as SpecOther.</summary>
        private KExpr SpecOfFieldReference(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                case IFieldReferenceOperation _:
                {
                    var (field, instance, onThis, instanceAt) = FieldOf(e, result, spec: true);
                    return Unbox(new KField { Field = field, Instance = instance, OnThis = onThis, At = e.Syntax, InstanceAt = instanceAt }, FieldType(field), e.Type);
                }
                default: return SpecOther(e, result);
            }
        }

        /// <summary>Spec of a parenthesized: its forms, in order; any other as SpecOther.</summary>
        private KExpr SpecOfParenthesized(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                case IParenthesizedOperation par: return Spec(par.Operand, result);
                default: return SpecOther(e, result);
            }
        }

        /// <summary>Spec of a conversion: its forms, in order; any other as SpecOther.</summary>
        private KExpr SpecOfConversion(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                case IConversionOperation conv when conv.Conversion.IsIdentity || IsIntegral(conv.Type) && IsIntegral(conv.Operand.Type) && (conv.Conversion.IsNumeric || conv.Type.TypeKind == TypeKind.Enum || conv.Operand.Type.TypeKind == TypeKind.Enum) &&
                                                    (conv.IsImplicit || Range(conv.Operand.Type).lo >= Range(conv.Type).lo && Range(conv.Operand.Type).hi <= Range(conv.Type).hi):
                    return Spec(conv.Operand, result);
                case IConversionOperation conv when Upcast(conv):
                    return conv.Operand.ConstantValue.HasValue ? new KLit("null") : Spec(conv.Operand, result);
                // (an unchecked cast to an integer type that doesn't hold all of the operand's, (uint)n: modulo its size, from its least)
                case IConversionOperation nc when !nc.IsChecked && nc.OperatorMethod == null && IsIntegral(nc.Type) && IsIntegral(nc.Operand.Type) && nc.Conversion.IsNumeric:
                    return SpecUncheckedNarrowing(nc, result);
                case IConversionOperation gc when gc.OperatorMethod != null && SpecSymbols.IsCsVerifyType(gc.OperatorMethod.ContainingType, "Ghost`1"):
                    return Spec(gc.Operand, result);
                default: return SpecOther(e, result);
            }
        }

        /// <summary>Spec of a unary: its forms, in order; any other as SpecOther.</summary>
        private KExpr SpecOfUnary(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Not: return new KOp("!", Spec(u.Operand, result));
                case IUnaryOperation bn when bn.OperatorKind == UnaryOperatorKind.BitwiseNegation && IsIntegral(bn.Type): return Complement(Spec(bn.Operand, result), bn.Type);
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Minus && _codeArith: return Arith("-", new KLit("0"), Spec(u.Operand, result), u.Type, u.Syntax, u.IsChecked);
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Minus: return new KOp("-", new KLit("0"), Spec(u.Operand, result));
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Plus: return Spec(u.Operand, result);
                default: return SpecOther(e, result);
            }
        }

        /// <summary>Spec of a conditional: its forms, in order; any other as SpecOther.</summary>
        private KExpr SpecOfConditional(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                case IConditionalOperation c when c.WhenFalse != null:
                    return new KOp("ite", Spec(c.Condition, result), Spec(c.WhenTrue, result), Spec(c.WhenFalse, result));
                default: return SpecOther(e, result);
            }
        }

        /// <summary>Spec of a binary: its forms, in order; any other as SpecOther.</summary>
        private KExpr SpecOfBinary(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                case IBinaryOperation b when b.OperatorMethod == null && !(IsString(b.LeftOperand.Type) && IsString(b.RightOperand.Type)):
                    return SpecBinary(b, result);
                case IBinaryOperation sb when IsString(sb.LeftOperand.Type) && IsString(sb.RightOperand.Type) &&
                                             (sb.OperatorMethod == null || IsString(sb.OperatorMethod.ContainingType)) &&
                                             sb.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals or BinaryOperatorKind.Add:
                    return RelationalStrings(sb, StringBinary(sb.OperatorKind, Spec(sb.LeftOperand, result), Spec(sb.RightOperand, result)), Spec(sb.LeftOperand, result), Spec(sb.RightOperand, result));
                case IBinaryOperation gb when gb.OperatorMethod != null && gb.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals &&
                                              (SpecSymbols.IsCsVerifyType(gb.OperatorMethod.ContainingType, "Seq`1") || SpecSymbols.IsCsVerifyType(gb.OperatorMethod.ContainingType, "Ghost`1") || IsObjSet(gb.OperatorMethod.ContainingType) ||
                                               SpecSymbols.IsCsVerifyType(gb.OperatorMethod.ContainingType, "Map`2")):
                    return new KOp(gb.OperatorKind == BinaryOperatorKind.Equals ? "==" : "!=", Spec(gb.LeftOperand, result), Spec(gb.RightOperand, result));
                case IBinaryOperation bb when bb.OperatorMethod != null && bb.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals && SpecSymbols.IsBag(bb.OperatorMethod.ContainingType):
                    return new KOp(bb.OperatorKind == BinaryOperatorKind.Equals ? "==" : "!=", Spec(bb.LeftOperand, result), Spec(bb.RightOperand, result));
                default: return SpecOther(e, result);
            }
        }

        /// <summary>Spec of a array element reference: its forms, in order; any other as SpecOther.</summary>
        private KExpr SpecOfArrayElementReference(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                case IArrayElementReferenceOperation el when IsArray(ActualArray(el.ArrayReference.Type)) && el.Indices.Length == 1:
                    return new KElem { Array = Spec(el.ArrayReference, result), Index = Spec(el.Indices[0], result), ArrayType = ActualArray(el.ArrayReference.Type), InSpec = true, At = el.Syntax, ArrayAt = el.ArrayReference.Syntax };
                default: return SpecOther(e, result);
            }
        }

        /// <summary>Spec of a invocation: its forms, in order; any other as SpecOther.</summary>
        private KExpr SpecOfInvocation(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                case IInvocationOperation sm when IntegerMath(sm):
                    return SpecIntegerMath(sm, result);
                case IInvocationOperation se when StringEquals(se) is (IOperation ea, IOperation eb):
                    return new KOp("streq", Spec(ea, result), Spec(eb, result));
                // (a collection's [Pure] member, List.IndexOf, Stack.Peek: a function of its models, its stub's contract its axioms)
                case IInvocationOperation cm when cm.Instance != null && CollectionFunction(cm.TargetMethod) is IMethodSymbol fm:
                    return SpecCollectionMethod(cm, fm, result);
                case IInvocationOperation st when !_isFunction(st.TargetMethod) && IsStub(st.TargetMethod.OriginalDefinition):
                    // (in an assertion of the body's: the proof assumes the stub)
                    if (st.Syntax.Ancestors().OfType<InvocationExpressionSyntax>().FirstOrDefault(i => i.Expression.ToString() is "Spec.Assert" or "Spec.Assume") != null) Assumed(st.TargetMethod.OriginalDefinition);
                    return StubCall(st, x => Spec(x, result));
                // (a list's model: its size, its version, its elements; Count and the indexer as their contracts say)
                case IInvocationOperation mo when SpecSymbols.IsModel(mo.TargetMethod.OriginalDefinition) && mo.Arguments.Length == 1 &&
                                                  CollectionOf(Unconverted(mo.Arguments[0].Value).Type) is INamedTypeSymbol mc && ModelOf(mo.TargetMethod.Name, mc) != null:
                    return Model(mo.TargetMethod.Name, mc, Spec(Unconverted(mo.Arguments[0].Value), result));
                // (a model a stub declares of its own, [Model] Len(b), At(b, i): a map of the objects, and of its other arguments)
                case IInvocationOperation um when SpecSymbols.IsModel(um.TargetMethod.OriginalDefinition) && um.TargetMethod.IsStatic && um.Arguments.Length >= 1 &&
                                                  um.TargetMethod.Parameters.Skip(1).All(x => Scalar(x.Type)) && InSubset(um.TargetMethod.ReturnType) && !um.TargetMethod.IsGenericMethod:
                    return SpecStubModel(um, result);
                // (a dictionary's ContainsKey and a set's Contains: its model, as their stubs say)
                case IInvocationOperation ck when ck.Instance != null && CollectionOf(ck.Instance.Type) is INamedTypeSymbol cd && ck.Arguments.Length == 1 &&
                                                  (CollectionKind(cd) == "Dictionary" && ck.TargetMethod.Name == "ContainsKey" || CollectionKind(cd) == "HashSet" && ck.TargetMethod.Name == "Contains"):
                    return SpecContainsKey(ck, cd, result);
                // (a list's Contains: an element below its Count equal to the value, as its stub says)
                case IInvocationOperation lcon when lcon.Instance != null && CollectionOf(lcon.Instance.Type) is INamedTypeSymbol lcl && CollectionKind(lcl) == "List" &&
                                                    lcon.TargetMethod.Name == "Contains" && lcon.Arguments.Length == 1:
                    return SpecListContains(lcon, lcl, result);
                case IInvocationOperation mu when SpecSymbols.IsCsVerifyType(mu.TargetMethod.ContainingType, "Map`2") && mu.TargetMethod.Name == "Update" && mu.Instance != null:
                    return new KOp("store", Spec(mu.Instance, result), Spec(mu.Arguments[0].Value, result), Spec(mu.Arguments[1].Value, result));
                case IInvocationOperation mk when SpecSymbols.IsCsVerifyType(mk.TargetMethod.ContainingType, "Map") && mk.TargetMethod.Name == "Const" && mk.Arguments.Length == 1:
                    return new KOp("map.const." + BoogieOf(Kind(Actual(mk.TargetMethod.TypeArguments[0]))), Spec(mk.Arguments[0].Value, result));
                case IInvocationOperation sq when SpecSymbols.IsCsVerifyType(sq.TargetMethod.ContainingType, "Seq`1") && sq.Instance != null:
                    return SpecSeqMember(sq, result);
                case IInvocationOperation sc when SpecSymbols.IsCsVerifyType(sc.TargetMethod.ContainingType, "Seq") && sc.TargetMethod.Name == "Const" && sc.Arguments.Length == 1:
                    return new KOp("seq.const", Spec(sc.Arguments[0].Value, result));
                case IInvocationOperation go when SpecSymbols.IsCsVerifyType(go.TargetMethod.ContainingType, "Ghost") && go.TargetMethod.Name == "Of" && go.Arguments.Length == 1:
                    return Spec(go.Arguments[0].Value, result);
                // (multisets: Spec.Multiset of an integer array, and Bag's values, maps from value to count)
                case IInvocationOperation ms when SpecSymbols.IsSpecClass(ms.TargetMethod.ContainingType) && ms.TargetMethod.Name == "Multiset" && ms.Arguments.Length == 2 &&
                                                  Unconverted(ms.Arguments[0].Value).Type is IArrayTypeSymbol { ElementType: var et } && IsIntegral(et):
                    return SpecMultiset(ms, result);
                case IInvocationOperation bo when SpecSymbols.IsBag(bo.TargetMethod.ContainingType) && Scalar(Unconverted(bo.Arguments.LastOrDefault()?.Value)?.Type ?? bo.TargetMethod.ContainingType) || bo.TargetMethod.Name == "Union" && SpecSymbols.IsBag(bo.TargetMethod.ContainingType):
                    return SpecBagCall(bo, result);
                // (an object's ownership tree: those with its root; without [Owns] fields, the object alone)
                case IInvocationOperation ot when SpecSymbols.IsCsVerifyType(ot.TargetMethod.ContainingType, "Own") && ot.TargetMethod.Name == "Tree" && ot.Arguments.Length == 1:
                    return KernelTypes.Trees ? new KOp("$tree", Spec(Unconverted(ot.Arguments[0].Value), result)) : new KOp("set.of", Spec(Unconverted(ot.Arguments[0].Value), result));
                case IInvocationOperation of when IsObjSet(of.TargetMethod.ContainingType) && of.TargetMethod.Name == "Of" && of.Arguments.Length == 1 &&
                                                  (IsRef(Unconverted(of.Arguments[0].Value).Type) || CollectionOf(Unconverted(of.Arguments[0].Value).Type) != null || Unconverted(of.Arguments[0].Value) is IInstanceReferenceOperation):
                    return new KOp("set.of", Spec(Unconverted(of.Arguments[0].Value), result));
                case IInvocationOperation add when IsObjSet(add.TargetMethod.ContainingType) && add.TargetMethod.Name == "Add" && add.Instance != null && IsRef(Unconverted(add.Arguments[0].Value).Type):
                    return new KOp("set.add", Spec(add.Instance, result), Spec(Unconverted(add.Arguments[0].Value), result));
                case IInvocationOperation has when IsObjSet(has.TargetMethod.ContainingType) && has.TargetMethod.Name == "Contains" && has.Instance != null && IsRef(Unconverted(has.Arguments[0].Value).Type):
                    return new KOp("sel", Spec(has.Instance, result), Spec(Unconverted(has.Arguments[0].Value), result));
                case IInvocationOperation sub when IsObjSet(sub.TargetMethod.ContainingType) && sub.TargetMethod.Name is "IsSubsetOf" or "IsDisjointFrom" && sub.Instance != null:
                    return new KOp(sub.TargetMethod.Name == "IsSubsetOf" ? "set.subset" : "set.disjoint", Spec(sub.Instance, result), Spec(sub.Arguments[0].Value, result));
                case IInvocationOperation union when IsObjSet(union.TargetMethod.ContainingType) && union.TargetMethod.Name == "Union" && union.Instance != null:
                    return new KOp("set.union", Spec(union.Instance, result), Spec(union.Arguments[0].Value, result));
                case IInvocationOperation acc when SpecSymbols.IsSpecClass(acc.TargetMethod.ContainingType) && acc.TargetMethod.Name == "Acc" &&
                                                   acc.Arguments.Length == 1 && IsOwnedClass(Unconverted(acc.Arguments[0].Value).Type):
                    return SpecAccOfObject(acc, result);
                case IInvocationOperation fa when SpecSymbols.IsSpecClass(fa.TargetMethod.ContainingType) && fa.TargetMethod.Name == "Acc" &&
                                                  fa.Arguments.Length == 2 && IsOwnedClass(Unconverted(fa.Arguments[0].Value).Type):
                    return SpecAccOfField(fa, result);
                case IInvocationOperation pc when SpecSymbols.IsPredicate(pc.TargetMethod.OriginalDefinition) && pc.TargetMethod.IsStatic:
                    _p.Preds.Add(pc.TargetMethod.OriginalDefinition);
                    return new KInst { Pred = pc.TargetMethod.OriginalDefinition, Args = pc.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => Spec(a.Value, result)).ToArray(), At = pc.Syntax };
                case IInvocationOperation inv when SpecSymbols.IsSpecClass(inv.TargetMethod.ContainingType):
                    return SpecOfSpecClass(inv, result);
                // (a virtual one of another object: the base member's function, which each override defines for objects of its class)
                case IInvocationOperation fn when _isFunction(fn.TargetMethod) && (fn.TargetMethod.IsStatic || fn.Instance != null &&
                                                  (!fn.TargetMethod.IsVirtual && !fn.TargetMethod.IsAbstract && !fn.TargetMethod.IsOverride || IsModeledClass(fn.Instance.Type))):
                    return SpecFunctionCall(fn, result);
                // (in a database query's lambda, a call EF translates to SQL that the kernel has no function of: the
                // database's function of its arguments, not C#'s (SQL's UPPER needn't be .NET's ToUpper))
                case IInvocationOperation dbf when DatabaseFunction(dbf):
                    return SpecDatabaseFunction(dbf, result);
                // (a call of what isn't [Pure], in an assertion of the body's: unknown, which warns)
                case IInvocationOperation np when _p.Result != null && !SpecSymbols.IsSpecClass(np.TargetMethod.ContainingType) && InSubset(np.Type) &&
                                                  !(_contractOf?.Invoke(np.TargetMethod.OriginalDefinition) is Contract nc && (nc.IsPure || nc.IsLemma)) && !_isFunction(np.TargetMethod) &&
                                                  np.Syntax.Ancestors().OfType<InvocationExpressionSyntax>().FirstOrDefault(i => i.Expression.ToString() is "Spec.Assert" or "Spec.Assume") != null:
                    return SpecImpureCall(np);
                default: return SpecOther(e, result);
            }
        }

        private KExpr SpecOfSpecClass(IInvocationOperation inv, IParameterSymbol result)
        {
            switch (inv.TargetMethod.Name)
            {
                case "Old":
                    _inOld++;
                    try { return new KOp("old", Spec(inv.Arguments[0].Value, result)); }
                    finally { _inOld--; }
                // (Dafny's fresh: every object in the set is new since entry)
                case "Fresh" when inv.Arguments.Length == 1 && IsObjSet(Unconverted(inv.Arguments[0].Value).Type):
                    // (a constructor's own object counts as new)
                    return _p.IsCtor ? new KOp("set.freshc", Spec(Unconverted(inv.Arguments[0].Value), result), new KOp("old", new KVar("$Alloc")), new KVar("this"))
                                     : new KOp("set.fresh", Spec(Unconverted(inv.Arguments[0].Value), result), new KOp("old", new KVar("$Alloc")));
                case "Equal" when inv.Arguments.Length == 2:
                    return EqualAs(Spec(inv.Arguments[0].Value, result), Spec(inv.Arguments[1].Value, result), Actual(IsGhost(inv.Arguments[0].Value.Type) ? GhostOf(inv.Arguments[0].Value.Type) : inv.Arguments[0].Value.Type));
                // (what a Func or an Action accepts and gives, the same in every state; whether it changes nothing)
                case "Pre" or "Post" or "Total" or "ChangesNothing" or "ReadsOf" when IsFunc(Unconverted(inv.Arguments[0].Value).Type):
                {
                    var f = Unconverted(inv.Arguments[0].Value);
                    var key = FuncKey(f.Type);
                    _p.DelegateKeys.Add(key);
                    var args = inv.Arguments.OrderBy(a => a.Parameter.Ordinal).Select((a, k) => k == 0 ? Spec(f, result) : Spec(a.Value, result)).ToList();
                    // (a parameter this method takes to be steady: in every state; any other, in this one)
                    // (one a lambda captures, of the method it's in: steady too, where nothing writes it)
                    bool steady = f is IParameterReferenceOperation sp && (SteadyParams(_m).Contains(sp.Parameter.OriginalDefinition) ||
                                  _capturedParams.Contains(sp.Parameter) && sp.Parameter.ContainingSymbol is IMethodSymbol om && SteadyParams(om).Contains(sp.Parameter.OriginalDefinition) && NeverWritten(sp.Parameter));
                    var stated = new[] { args[0], new KOp("$state") }.Concat(args.Skip(1)).ToArray();
                    switch (inv.TargetMethod.Name)
                    {
                        case "Pre": return steady ? new KOp("$pre." + key, args.ToArray()) : new KOp("$preS." + key, stated);
                        case "Post": return steady ? new KOp("$post." + key, args.ToArray()) : new KOp("$postS." + key, stated);
                        case "ReadsOf": return new KOp("$readsS." + key, stated);
                        case "Total" when steady: return new KOp("$total." + key, args[0]);
                        // (of one that may read state: that it accepts every argument in this one)
                        case "Total":
                        {
                            var ps = ((INamedTypeSymbol)f.Type).DelegateInvokeMethod.Parameters.Select((p, k) => ("x$tot" + k, TypeOf(p.Type))).ToList();
                            return Forall(ps, new KOp("$preS." + key, new[] { args[0], new KOp("$state") }.Concat(ps.Select(p => (KExpr)new KVar(p.Item1))).ToArray()));
                        }
                        default: return new KOp("$nochange", args[0]);
                    }
                }
                // (what a delegate reads, or may change, is within a frame of its arguments)
                case "Reads" or "Changes" when inv.Arguments.Length == 2 && IsFunc(Unconverted(inv.Arguments[0].Value).Type):
                {
                    var f = Unconverted(inv.Arguments[0].Value);
                    var key = FuncKey(f.Type);
                    _p.DelegateKeys.Add(key);
                    var given = Unconverted(inv.Arguments[1].Value);
                    var ps = new List<(string name, string type)>();
                    KExpr within;
                    if (given is IDelegateCreationOperation gd && LambdaOf(gd.Target) is IAnonymousFunctionOperation gf &&
                        gf.Body.Operations.Length == 1 && gf.Body.Operations[0] is IReturnOperation gr)
                    {
                        foreach (var p in gf.Symbol.Parameters) ps.Add(("q$" + p.Name, TypeOf(p.Type)));
                        within = Spec(gr.ReturnedValue, null);
                    }
                    else within = Spec(given, result);
                    var xs = ps.Select(p => (KExpr)new KVar(p.name)).ToArray();
                    var d = Spec(f, result);
                    var set = inv.TargetMethod.Name == "Reads"
                        ? new KOp("$readsS." + key, new[] { d, new KOp("$state") }.Concat(xs).ToArray())
                        : new KOp("$frame." + key, new[] { d }.Concat(xs).ToArray());
                    return Forall(ps, new KOp("set.subset", set, within));
                }
                // (a foreach's index: of its element in the body, the number gone through at its head; through an
                // enumerator too, as it counts the edges back to the head)
                case "Index" when Unconverted(inv.Arguments[0].Value) is ILocalReferenceOperation ix && _forEachOf.TryGetValue(ix.Local, out var fx):
                    return new KVar(fx.Index);
                // (allocated during the call)
                case "Fresh" when IsRef(Unconverted(inv.Arguments[0].Value).Type) ||
                                  IsRef(ActualArray(Unconverted(inv.Arguments[0].Value).Type)) || IsRef(Constructed(Unconverted(inv.Arguments[0].Value).Type)):
                    // (its argument read now: only the allocated set is as it was)
                    return new KOp("&&", new KOp("!=", Spec(Unconverted(inv.Arguments[0].Value), result), new KLit("null")),
                        new KOp("!", new KOp("sel", new KOp("old", new KVar("$Alloc")), Spec(Unconverted(inv.Arguments[0].Value), result))));
                case "Acc" or "AccRead" when IsArray(Unconverted(inv.Arguments[0].Value).Type) && inv.Arguments.Length is 1 or 3:
                {
                    var arr = Spec(Unconverted(inv.Arguments[0].Value), result);
                    return new KCells
                    {
                        Arr = arr, Read = inv.TargetMethod.Name == "AccRead", At = inv.Syntax,
                        Lo = inv.Arguments.Length == 1 ? new KLit("0") : Spec(inv.Arguments[1].Value, result),
                        Hi = inv.Arguments.Length == 1 ? new KOp("len", arr) : Spec(inv.Arguments[2].Value, result),
                    };
                }
                case "Result": return new KVar("result");
                case "Forall": case "Exists" when inv.Arguments.Length == 3:
                {
                    var lo = Spec(inv.Arguments[0].Value, result);
                    var hi = Spec(inv.Arguments[1].Value, result);
                    var fn = (inv.Arguments[2].Value as IDelegateCreationOperation)?.Target as IAnonymousFunctionOperation
                             ?? throw new NotTranslated("a quantifier without a lambda");
                    if (!(fn.Body.Operations.Length == 1 && fn.Body.Operations[0] is IReturnOperation ret)) throw new NotTranslated("a quantifier's body");
                    var q = "q$" + fn.Symbol.Parameters[0].Name;
                    return new KQuant
                    {
                        Forall = inv.TargetMethod.Name == "Forall", Var = q,
                        Range = new KOp("&&", new KOp("<=", lo, new KVar(q)), new KOp("<", new KVar(q), hi)),
                        Body = Spec(ret.ReturnedValue, result),
                    };
                }
                default: throw new NotTranslated("Spec." + inv.TargetMethod.Name + " in a specification");
            }
        }

        private KExpr SpecBagCall(IInvocationOperation bo, IParameterSymbol result)
        {
            var self = bo.Instance == null ? null : Spec(bo.Instance, result);
            var arg = bo.Arguments.Length == 1 ? Spec(Unconverted(bo.Arguments[0].Value), result) : null;
            switch (bo.TargetMethod.Name)
            {
                case "Of" when self == null && arg != null: return new KOp("$badd", new KLit("$bag.empty"), arg);
                case "Count" when self != null: return new KOp("sel", self, arg);
                case "Contains" when self != null: return new KOp("<", new KLit("0"), new KOp("sel", self, arg));
                case "Add" when self != null: return new KOp("$badd", self, arg);
                case "Union" when self != null: return new KOp("$bunion", self, arg);
                default: throw new NotTranslated("Bag's " + bo.TargetMethod.Name);
            }
        }

        private KExpr SpecCollectionMethod(IInvocationOperation cm, IMethodSymbol fm, IParameterSymbol result)
        {
            var ct = (INamedTypeSymbol)fm.ContainingType;
            foreach (var model in ModelsOf(ct).Concat(Checks.StubModels(fm, _contractOf?.Invoke(fm)))) _p.Models[model.Name] = model;
            _p.Stubs.Add(fm);
            var ordered = cm.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            var args = ordered.Select(a => (KExpr)(CustomEquality(fm.Parameters[a.Parameter.Ordinal].Type) ? Spec(a.Value, result) : Keyed(Spec(a.Value, result), fm.Parameters[a.Parameter.Ordinal].Type))).ToArray();
            return new KFnCall { Callee = fm, Receiver = Spec(cm.Instance, result), ReceiverAt = cm.Instance.Syntax, Args = args, At = cm.Syntax, Stub = true };
        }

        /// <summary>Spec of a coalesce: its forms, in order; any other as SpecOther.</summary>
        private KExpr SpecOfCoalesce(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                // (a ?? b of a reference or a string: a where it isn't null; of a nullable value: its value, or b)
                case ICoalesceOperation co when (IsNullable(co.Value.Type) && !IsNullableValue(co.Value.Type) || IsNullableValue(co.Value.Type) && !IsNullableValue(co.Type)) && InSubset(co.Type):
                    return SpecCoalesce(co, result);
                default: return SpecOther(e, result);
            }
        }

        /// <summary>Spec of a conditional access: its forms, in order; any other as SpecOther.</summary>
        private KExpr SpecOfConditionalAccess(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                // (a?.m: null where a is, else m of it; of a value, that value as a nullable one)
                case IConditionalAccessOperation ca when IsNullable(ca.Operation.Type) && !IsNullableValue(ca.Operation.Type) && InSubset(ca.Type) &&
                                                         (IsNullable(ca.Type) && !IsNullableValue(ca.WhenNotNull.Type) || IsNullableValue(ca.Type) && Scalar(ca.WhenNotNull.Type)):
                    return SpecConditionalAccess(ca, result);
                default: return SpecOther(e, result);
            }
        }

        /// <summary>Spec of a conditional access instance: its forms, in order; any other as SpecOther.</summary>
        private KExpr SpecOfConditionalAccessInstance(IOperation e, IParameterSymbol result)
        {
            switch (e)
            {
                case IConditionalAccessInstanceOperation when _conditionalInstances.Count > 0: return _conditionalInstances.Peek();
                default: return SpecOther(e, result);
            }
        }

        /// <summary>Spec of an operation none of the forms above is.</summary>
        private KExpr SpecOther(IOperation e, IParameterSymbol result)
        {
            throw new NotTranslated("in a specification: " + e.Kind + " '" + e.Syntax + "'");
        }

        private KExpr SpecListContains(IInvocationOperation lcon, INamedTypeSymbol lcl, IParameterSymbol result)
        {
            var items = ModelOf("Items", lcl);
            _p.Models[items.Name] = items;
            _p.Models[SizeMap] = ModelOf("Size", lcl);
            var of = Spec(lcon.Instance, result);
            var x = Spec(lcon.Arguments[0].Value, result);
            var v = "q$c" + _linq++;
            return new KOp("&&", new KOp("!=", of, new KLit("null")), new KQuant { Forall = false, Var = v,
                Range = new KOp("&&", new KOp("<=", new KLit("0"), new KVar(v)), new KOp("<", new KVar(v), new KOp("sel", new KVar(SizeMap), of))),
                Body = SameValue(new KOp("sel", new KVar(items.Name), of, new KVar(v)), x, lcl.TypeArguments[0]) });
        }

        private KExpr SpecContainsKey(IInvocationOperation ck, INamedTypeSymbol cd, IParameterSymbol result)
        {
            var model = ModelOf(CollectionKind(cd) == "Dictionary" ? "Domain" : "Members", cd);
            _p.Models[model.Name] = model;
            var of = Spec(ck.Instance, result);
            return new KOp("&&", new KOp("!=", of, new KLit("null")), new KOp("sel", new KVar(model.Name), of, Keyed(Spec(ck.Arguments[0].Value, result), ck.Arguments[0].Value.Type)));
        }

        private KExpr SpecCollectionIndexer(IPropertyReferenceOperation li, INamedTypeSymbol ic, IParameterSymbol result)
        {
            bool dict = CollectionKind(ic) == "Dictionary";
            var items = ModelOf(dict ? "Entries" : "Items", ic);
            var bound = ModelOf(dict ? "Domain" : "Size", ic);
            _p.Models[items.Name] = items;
            _p.Models[bound.Name] = bound;
            return new KElem { Model = items.Name, Domain = dict ? bound.Name : null, Array = Spec(li.Instance, result), Index = dict ? Keyed(Spec(li.Arguments[0].Value, result), li.Arguments[0].Value.Type) : Spec(li.Arguments[0].Value, result),
                               InSpec = true, At = li.Syntax, ArrayAt = li.Instance.Syntax };
        }

        private KExpr SpecImpureProperty(IPropertyReferenceOperation npr)
        {
            var span = npr.Syntax.GetLocation().GetLineSpan();
            if (!_p.Warnings.Any(w => w.Span.Equals(span)))
                _p.Warnings.Add(new VerificationDiagnostic("CSV1900", false, $"'{npr.Property.Name}' is not a [Pure] property and cannot be used in a specification; treated as unknown", span));
            return new KVar(Declare("t$" + _temps++, npr.Type));
        }

        private KExpr SpecLibraryProperty(IPropertyReferenceOperation slp)
        {
            var span = slp.Syntax.GetLocation().GetLineSpan();
            if (!_p.Warnings.Any(w => w.Span.Equals(span)))
                _p.Warnings.Add(new VerificationDiagnostic("CSV1901", true, $"property '{slp.Property.Name}' is not supported: only auto-properties, properties with code, and properties of immutable types are", span));
            // (in an assertion, a value of its own; in a contract, which is outside the body, its type's default: the error stands either way)
            if (slp.Syntax.Ancestors().OfType<InvocationExpressionSyntax>().FirstOrDefault(i => i.Expression.ToString() is "Spec.Assert" or "Spec.Assume") != null)
                return new KVar(Declare("t$" + _temps++, slp.Type));
            return Default(slp.Type) ?? throw new NotTranslated("a default of " + slp.Type);
        }

        private KExpr SpecImpureCall(IInvocationOperation np)
        {
            var span = np.Syntax.GetLocation().GetLineSpan();
            if (!_p.Warnings.Any(w => w.Span.Equals(span)))
                _p.Warnings.Add(new VerificationDiagnostic("CSV1900", false, $"'{np.TargetMethod.Name}' is not [Pure] and cannot be used in a specification; treated as unknown", span));
            return new KVar(Declare("t$" + _temps++, np.Type));
        }

        private KExpr SpecDatabaseFunction(IInvocationOperation dbf, IParameterSymbol result)
        {
            var m = dbf.TargetMethod;
            var args = (dbf.Instance == null ? new IOperation[0] : new[] { dbf.Instance }).Concat(dbf.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => a.Value)).ToList();
            var name = "$db." + Ident(m.ContainingType.ToDisplayString() + "." + m.Name) + "." + string.Join("_", args.Select(a => TypeOf(a.Type).Replace("[", "_").Replace("]", "_")));
            _p.Functions.Add($"function {name}({string.Join(", ", args.Select((a, k) => $"a{k}: {TypeOf(a.Type)}"))}): {TypeOf(m.ReturnType)};");
            return new KOp(name, args.Select(a => Spec(a, result)).ToArray());
        }

        private KExpr SpecConditionalAccess(IConditionalAccessOperation ca, IParameterSymbol result)
        {
            var r = Spec(ca.Operation, result);
            _conditionalInstances.Push(r);
            KExpr then;
            try { then = Spec(ca.WhenNotNull, result); }
            finally { _conditionalInstances.Pop(); }
            if (IsNullableValue(ca.Type) && !IsNullableValue(ca.WhenNotNull.Type)) then = NullableOf(then, ca.Type);
            return new KOp("ite", new KOp("!=", r, new KLit("null")), then, new KLit("null"));
        }

        private KExpr SpecCoalesce(ICoalesceOperation co, IParameterSymbol result)
        {
            var v = Spec(co.Value, result);
            var w = Spec(co.WhenNull, result);
            return new KOp("ite", new KOp("!=", v, new KLit("null")), IsNullableValue(co.Value.Type) ? NullableValue(v, co.Value.Type) : v, w);
        }

        private KExpr SpecFunctionCall(IInvocationOperation fn, IParameterSymbol result)
        {
            bool onThis = fn.Instance is IInstanceReferenceOperation;
            var call = new KFnCall
            {
                Callee = fn.TargetMethod.OriginalDefinition, Receiver = fn.Instance == null ? null : Spec(fn.Instance, result), ReceiverIsThis = onThis, ReceiverAt = fn.Instance?.Syntax,
                Args = fn.Arguments.OrderBy(a => a.Parameter.Ordinal)
                         .Select(a => Box(Spec(a.Value, result), fn.TargetMethod.OriginalDefinition.Parameters[a.Parameter.Ordinal].Type, a.Parameter.Type)).ToArray(),
                At = fn.Syntax,
            };
            return Unbox(call, fn.TargetMethod.OriginalDefinition.ReturnType, fn.TargetMethod.ReturnType);
        }

        private KExpr SpecAccOfField(IInvocationOperation fa, IParameterSymbol result)
        {
            var target = Unconverted(fa.Arguments[0].Value);
            // (only of a sealed class without an [Invariant], and not an [Owns] field: the rest is reported)
            if (!(fa.Arguments[1].Value.ConstantValue is { HasValue: true, Value: string name }) || !(target.Type is INamedTypeSymbol { IsSealed: true } t) ||
                DataTypes.Invariants(t).Any() || !(WholeFields(t).FirstOrDefault(x => x.Name == name) is ISymbol field))
            {
                // (CSV1016, in the method's own contract; a permission of nothing)
                var type = target.Type;
                var fname = fa.Arguments[1].Value.ConstantValue.Value as string;
                var why = fname == null || WholeFields(type).All(x => x.Name != fname) ? $"{type.Name} has no field '{fname}'"
                        : !(type is INamedTypeSymbol { IsSealed: true }) ? $"{type.Name} is not sealed (a subclass would have fields this cannot account for)"
                        : $"{type.Name} has an [Invariant], which is about the whole object";
                var span = fa.Syntax.GetLocation().GetLineSpan();
                if (_p.Result != null && !_p.Warnings.Any(w => w.Span.Equals(span) && w.Id == "CSV1016"))
                    _p.Warnings.Add(new VerificationDiagnostic("CSV1016", true, $"Spec.Acc of a single field: {why}", span));
                return new KLit("true");
            }
            return new KFieldAcc { Obj = Spec(target, result), Field = field, Type = target.Type, At = fa.Syntax };
        }

        private KExpr SpecAccOfObject(IInvocationOperation acc, IParameterSymbol result)
        {
            var target = Unconverted(acc.Arguments[0].Value);
            return new KAcc { Obj = Spec(target, result), Type = target.Type, At = acc.Syntax };
        }

        private KExpr SpecMultiset(IInvocationOperation ms, IParameterSymbol result)
        {
            var arr = Unconverted(ms.Arguments[0].Value);
            var count = ms.Arguments.First(x => x.Parameter.Ordinal == 1).Value;
            return new KMultiset { Array = Spec(arr, result), Count = Spec(count, result), ArrayType = arr.Type, At = ms.Syntax,
                                   Levels = count.ConstantValue.Value is int k && k >= 0 && k <= 32 ? Math.Max(k, 1) : 1 };
        }

        private KExpr SpecSeqMember(IInvocationOperation sq, IParameterSymbol result)
        {
            var a = sq.Arguments.OrderBy(x => x.Parameter.Ordinal).Select(x => Spec(x.Value, result)).ToArray();
            var self = Spec(sq.Instance, result);
            return sq.TargetMethod.Name switch
            {
                "Update" => new KOp("store", self, a[0], a[1]),
                "Drop" => new KOp("seq.drop", self, a[0]),
                "Concat" => new KOp("seq.concat", self, a[0], a[1]),
                _ => throw new NotTranslated("Seq." + sq.TargetMethod.Name),
            };
        }

        private KExpr SpecStubModel(IInvocationOperation um, IParameterSymbol result)
        {
            var ordered = um.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
            var model = UserModel(um.TargetMethod.OriginalDefinition);
            _p.Models[model.Name] = model;
            var args = new[] { new KVar(model.Name), Spec(Unconverted(ordered[0].Value), result) }.Concat(ordered.Skip(1).Select(a => Spec(a.Value, result))).ToArray();
            return new KOp("sel", args);
        }

        private KExpr SpecIntegerMath(IInvocationOperation sm, IParameterSymbol result)
        {
            var v = sm.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => Spec(a.Value, result)).ToArray();
            return sm.TargetMethod.Name == "Abs" ? new KOp("ite", new KOp(">=", v[0], new KLit("0")), v[0], new KOp("-", new KLit("0"), v[0])) : MinMax(sm.TargetMethod.Name, v[0], v[1]);
        }

        private KExpr SpecBinary(IBinaryOperation b, IParameterSymbol result)
        {
            var l = Spec(b.LeftOperand, result);
            var r = Spec(b.RightOperand, result);
            if (IsBitwise(b.OperatorKind) && IsIntegral(b.Type)) return Bitwise(b.OperatorKind, l, r, b.Type, inSpec: true);
            return b.OperatorKind switch
            {
                BinaryOperatorKind.Add when _codeArith => Arith("+", l, r, b.Type, b.Syntax, b.IsChecked),
                BinaryOperatorKind.Subtract when _codeArith => Arith("-", l, r, b.Type, b.Syntax, b.IsChecked),
                BinaryOperatorKind.Multiply when _codeArith => Arith("*", l, r, b.Type, b.Syntax, b.IsChecked),
                BinaryOperatorKind.Divide when _codeArith => Arith("/", l, r, b.Type, b.Syntax, b.IsChecked),
                BinaryOperatorKind.Remainder when _codeArith => Arith("%", l, r, b.Type, b.Syntax, b.IsChecked),
                BinaryOperatorKind.Add => new KOp("+", l, r),
                BinaryOperatorKind.Subtract => new KOp("-", l, r),
                BinaryOperatorKind.Multiply => new KOp("*", l, r),
                BinaryOperatorKind.Divide => new KArith { Op = "/", Left = l, Right = r, Type = b.Type, Mode = KMode.Math, At = b.Syntax },
                BinaryOperatorKind.Remainder => new KArith { Op = "%", Left = l, Right = r, Type = b.Type, Mode = KMode.Math, At = b.Syntax },
                BinaryOperatorKind.Equals => new KOp("==", l, r),
                BinaryOperatorKind.NotEquals => new KOp("!=", l, r),
                BinaryOperatorKind.LessThan => new KOp("<", l, r),
                BinaryOperatorKind.LessThanOrEqual => new KOp("<=", l, r),
                BinaryOperatorKind.GreaterThan => new KOp(">", l, r),
                BinaryOperatorKind.GreaterThanOrEqual => new KOp(">=", l, r),
                BinaryOperatorKind.ConditionalAnd => new KOp("&&", l, r),
                BinaryOperatorKind.ConditionalOr => new KOp("||", l, r),
                BinaryOperatorKind.And => new KOp("&", l, r),
                BinaryOperatorKind.Or => new KOp("|", l, r),
                BinaryOperatorKind.ExclusiveOr => new KOp("!=", l, r),
                _ => throw new NotTranslated("the operator " + b.OperatorKind),
            };
        }

        private KExpr SpecUncheckedNarrowing(IConversionOperation nc, IParameterSymbol result)
        {
            var (lo, hi) = Range(nc.Type);
            var size = Number(hi - lo + 1);
            return new KOp("+", new KOp("emod", new KOp("-", Spec(nc.Operand, result), Number(lo)), size), Number(lo));
        }

        private KExpr SpecStubParameter(IParameterReferenceOperation p)
        {
            int shift = _p.HasThis ? 1 : 0;
            if (shift == 1 && p.Parameter.Ordinal == 0) return new KVar("this");
            return new KVar(Local(_m.Parameters[p.Parameter.Ordinal - shift]));
        }
    }
}
