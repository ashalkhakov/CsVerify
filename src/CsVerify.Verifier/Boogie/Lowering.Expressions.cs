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
    /// <summary>Expressions in code: operators, conversions, fields, strings, tuples, collections through their interfaces.</summary>
    internal sealed partial class Lowering
    {
        /// <summary>A static readonly field of the program's that the kernel doesn't have as a field: its value, a constant of the run's ($sf).</summary>
        private static KExpr StaticReadonly(IFieldSymbol f)
        {
            if (f.DeclaringSyntaxReferences.Length == 0 || f.IsConst || IsField(f) || IsLockObject(f) || !InSubset(f.Type)) return null;
            var kind = TypeOf(f.Type) switch { "Ref" => "Ref", "int" => "Int", "bool" => "Bool", _ => null };
            if (kind == null) return null;
            var ids = KernelTypes.StaticReadonlyIds ??= new Dictionary<string, int>();
            var key = f.OriginalDefinition.ToDisplayString();
            if (!ids.TryGetValue(key, out var k)) ids[key] = k = ids.Count;
            if (kind == "Ref" && IsNullable(f.Type) && NotNullable(f.Type) && StaticStartsWithObject(f)) (KernelTypes.StaticReadonlyNonNull ??= new HashSet<int>()).Add(k);
            return new KOp("$sf" + kind, new KLit(k.ToString()));
        }

        /// <summary>A tuple whose elements compare as values: integers, enums, chars and bools.</summary>
        private static bool TupleComparable(ITypeSymbol t) =>
            t is INamedTypeSymbol { IsTupleType: true } n && n.TupleElements.All(e => IsIntegral(e.Type) || e.Type.SpecialType == SpecialType.System_Boolean);

        /// <summary>A tuple's elements, in order: a tuple written here, (x, y), each value; any other, each item of it.</summary>
        private List<KExpr> TupleParts(IOperation op, Func<IOperation, KExpr> lower, bool inSpec)
        {
            if (Unconverted(op) is ITupleOperation lit) return lit.Elements.Select(e => Operand(e, lower, inSpec)).ToList();
            var v = Operand(op, lower, inSpec);
            return Enumerable.Range(0, ((INamedTypeSymbol)op.Type).TupleElements.Length).Select(k => TupleItem(v, op.Type, k)).ToList();
        }

        /// <summary>A new array of <paramref name="length"/> elements, src's from <paramref name="start"/> on (Clone, a slice).</summary>
        private KExpr CopyOf(KExpr src, KExpr start, KExpr length, ITypeSymbol arrayType, SyntaxNode at)
        {
            var copy = Declare("t$" + _temps++, arrayType);
            Emit(new KNew { Var = copy, ArrayType = arrayType, Size = length });
            var map = Elements(arrayType);
            var row = new KVar(LinqMap("[int]" + ElementValue(map)));
            Emit(new KRow { Map = map, Ref = new KVar(copy), Value = row });
            var i = new KVar("i$k");
            Emit(new KSpecStmt { Spec = new KQuant { Forall = true, Var = "i$k", Body = new KOp("==", new KOp("sel", row, i), new KOp("sel", new KVar(map), src, new KOp("+", start, i))) },
                                 Assume = true, Free = true, At = at, ArgumentAt = at });
            return new KVar(copy);
        }

        private static bool AnonymousAsObject(IOperation o) =>
            o is IConversionOperation { Conversion.IsReference: true } c && c.Operand.Type is INamedTypeSymbol { IsAnonymousType: true } && !c.Type.IsAnonymousType;

        /// <summary>An anonymous object compared with null (an OrDefault's none): the anonymous object, and whether it's ==.</summary>
        private static (IOperation anonymous, bool equals)? AnonymousVsNull(IOperation e) =>
            e is IBinaryOperation b && b.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals && b.OperatorMethod == null &&
            (AnonymousAsObject(b.LeftOperand) && Unconverted(b.RightOperand).ConstantValue is { HasValue: true, Value: null } ? Unconverted(b.LeftOperand) :
             AnonymousAsObject(b.RightOperand) && Unconverted(b.LeftOperand).ConstantValue is { HasValue: true, Value: null } ? Unconverted(b.RightOperand) : null) is IOperation a
                ? (a, b.OperatorKind == BinaryOperatorKind.Equals) : null;

        /// <summary>Math.Max, Math.Min (two arguments) and Math.Abs (one) of an integral type.</summary>
        private static bool IntegerMath(IInvocationOperation inv) =>
            inv.TargetMethod.ContainingType?.ToDisplayString() == "System.Math" && IsIntegral(inv.Type) &&
            (inv.TargetMethod.Name is "Max" or "Min" && inv.Arguments.Length == 2 || inv.TargetMethod.Name == "Abs" && inv.Arguments.Length == 1);

        private static KExpr MinMax(string name, KExpr a, KExpr b) => new KOp("ite", new KOp(name == "Max" ? ">=" : "<=", a, b), a, b);

        // ------------------------------------------------------------------ locks

        private readonly Dictionary<CaptureId, IOperation> _captured = new Dictionary<CaptureId, IOperation>();

        /// <summary>A positional property as the type it's read at has it (its own or a base's).</summary>
        private static IPropertySymbol Actual(ITypeSymbol t, string name)
        {
            for (var s = t as INamedTypeSymbol; s != null; s = s.BaseType)
                if (s.GetMembers(name).OfType<IPropertySymbol>().FirstOrDefault() is IPropertySymbol p) return p;
            return null;
        }

        /// <summary>An operand that's tested more than once: in code, in a variable of its own.</summary>
        private KExpr Operand(IOperation op, Func<IOperation, KExpr> lower, bool inSpec)
        {
            var v = lower(op);
            if (inSpec || v is KVar || v is KLit) return v;
            var t = Declare("t$" + _temps++, op.Type);
            Emit(new KAssign { Var = t, Value = v });
            return new KVar(t);
        }

        /// <summary>
        /// A collection: of the subset's values, or, in a collection member's stub (written over List&lt;T&gt;), the
        /// collection it is for; null for anything else.
        /// </summary>
        private INamedTypeSymbol CollectionOf(ITypeSymbol t)
        {
            if (IsCollection(t)) return (INamedTypeSymbol)t;
            if (CollectionKind(t) != null && ((INamedTypeSymbol)t).TypeArguments.Any(a => a is ITypeParameterSymbol) && _contract.IsStub && IsCollection(_m.ContainingType) &&
                SymbolEqualityComparer.Default.Equals(t.OriginalDefinition, _m.ContainingType.OriginalDefinition))
                return (INamedTypeSymbol)_m.ContainingType;
            return null;
        }

        /// <summary>A type as it is here: in a collection member's stub, its type parameters are the collection's arguments.</summary>
        /// <summary>A type as it is here, an array of a stub's T too (List&lt;int&gt;'s ToArray gives an int[]).</summary>
        private ITypeSymbol ActualArray(ITypeSymbol t) =>
            t is IArrayTypeSymbol { ElementType: ITypeParameterSymbol e, Rank: 1 } && !SymbolEqualityComparer.Default.Equals(Actual(e), e)
                ? KernelTypes.Compilation.CreateArrayTypeSymbol(Actual(e)) : t;

        /// <summary>A generic type of a stub's type parameters (List&lt;T&gt; in a list's stub), as this collection's are.</summary>
        private ITypeSymbol Constructed(ITypeSymbol t) =>
            t is INamedTypeSymbol { IsGenericType: true } n && n.TypeArguments.Any(a => a is ITypeParameterSymbol) && n.TypeArguments.Select(Actual).ToArray() is var args && !args.Any(a => a is ITypeParameterSymbol)
                ? n.OriginalDefinition.Construct(args) : t;

        private ITypeSymbol Actual(ITypeSymbol t) =>
            t is ITypeParameterSymbol tp && _contract.IsStub && IsCollection(_m.ContainingType) && tp.Ordinal < ((INamedTypeSymbol)_m.ContainingType).TypeArguments.Length
                ? ((INamedTypeSymbol)_m.ContainingType).TypeArguments[tp.Ordinal] : t;

        /// <summary>A collection interface's Count or element: of an array, a modeled collection, or the state (unknown at each read where the program implements it).</summary>
        private KExpr Ifc(IPropertyReferenceOperation p, KExpr index, KExpr of, bool inSpec)
        {
            var ifc = (INamedTypeSymbol)p.Property.ContainingType;
            var element = ifc.TypeArguments[0];
            // (the program's own implementations of any of these interfaces make reads through them unknown)
            bool fresh = new[] { "IList", "IReadOnlyList", "ICollection", "IReadOnlyCollection" }.Any(n =>
                KernelTypes.Compilation.GetTypeByMetadataName($"System.Collections.Generic.{n}`1") is INamedTypeSymbol d && ImplementedHere(d));
            // (in a specification, a read of the state's model: some value, which code's reads, each unknown, needn't agree with)
            if (inSpec) fresh = false;
            var list = (INamedTypeSymbol)KernelTypes.Compilation.GetTypeByMetadataName("System.Collections.Generic.List`1").Construct(element);
            foreach (var m in ModelsOf(list)) _p.Models[m.Name] = m;
            _p.UsesState = true;
            return new KIfc { Item = index != null, Of = of, Index = index, Element = element, Fresh = fresh, At = p.Syntax, OfAt = p.Instance.Syntax };
        }

        private KExpr Model(string name, INamedTypeSymbol collection, KExpr of)
        {
            var model = ModelOf(name, collection) ?? throw new NotTranslated("the model " + name);
            _p.Models[model.Name] = model;
            return new KOp("sel", new KVar(model.Name), of);
        }

        /// <summary>A value of locals, parameters, constants and array elements, whose locals and parameters the expression doesn't write.</summary>
        private static bool Steady(IOperation op, ExpressionSyntax during)
        {
            var names = new HashSet<string>();
            bool Simple(IOperation o)
            {
                switch (o)
                {
                    case IConversionOperation { IsImplicit: true } c: return Simple(c.Operand);
                    case ILocalReferenceOperation l: names.Add(l.Local.Name); return true;
                    case IParameterReferenceOperation pr: names.Add(pr.Parameter.Name); return true;
                    case IInstanceReferenceOperation _: return true;
                    case IFieldReferenceOperation { Field.IsReadOnly: true } f: return f.Instance == null || Simple(f.Instance);
                    case IArrayElementReferenceOperation ae: return Simple(ae.ArrayReference) && ae.Indices.All(Simple);
                    default: return o.ConstantValue.HasValue;
                }
            }
            if (!Simple(op)) return false;
            bool Names(ExpressionSyntax e) => e is IdentifierNameSyntax n && names.Contains(n.Identifier.Text);
            return !during.DescendantNodesAndSelf().OfType<AssignmentExpressionSyntax>().Any(a => Names(a.Left)) &&
                   !during.DescendantNodesAndSelf().OfType<PostfixUnaryExpressionSyntax>().Any(u => Names(u.Operand)) &&
                   !during.DescendantNodesAndSelf().OfType<PrefixUnaryExpressionSyntax>().Any(u => Names(u.Operand)) &&
                   !during.DescendantNodesAndSelf().OfType<ArgumentSyntax>().Any(a => !a.RefKindKeyword.IsKind(SyntaxKind.None) && Names(a.Expression));
        }

        private string Capture(CaptureId id, ITypeSymbol type)
        {
            if (type == null || !InSubset(type)) throw new NotTranslated("a capture of " + type);
            return Declare("c$" + id.GetHashCode(), type);
        }

        /// <summary>A field access's field, its object (null for a static field), whether that is this, and where it is.</summary>
        private (ISymbol field, KExpr instance, bool onThis, SyntaxNode at) FieldOf(IOperation access, IParameterSymbol specResult = null, bool spec = false)
        {
            var (symbol, instance) = access switch
            {
                IFieldReferenceOperation f => ((ISymbol)f.Field, f.Instance),
                IPropertyReferenceOperation p when p.Arguments.Length == 0 => (p.Property, p.Instance),
                _ => throw new NotTranslated(access.Kind.ToString()),
            };
            if (!IsField(symbol)) throw new NotTranslated("the member " + symbol.Name);
            symbol = symbol.OriginalDefinition;
            _p.Fields.Add(symbol);
            var name = (access.Syntax as MemberAccessExpressionSyntax)?.Name ?? access.Syntax;
            if (symbol.IsStatic) { if (!spec) Held(symbol, null, name); return (symbol, null, false, null); }
            if (instance is IInstanceReferenceOperation { ReferenceKind: InstanceReferenceKind.ContainingTypeInstance })
            {
                if (!spec) Held(symbol, new KVar("this"), name);
                return (symbol, new KVar("this"), true, instance.Syntax);
            }
            var o = spec ? Spec(instance, specResult) : Expr(instance);
            if (!spec) Held(symbol, o, name);
            return (symbol, o, false, instance.Syntax);
        }

        // ------------------------------------------------------------------ expressions (run time)

        private KMode Mode(SyntaxNode at, bool isChecked) =>
            !isChecked && InUnchecked(at) ? KMode.Unchecked : _p.Ghost ? KMode.Math : isChecked ? KMode.Checked : KMode.Default;

        /// <summary>
        /// Operands, in C#'s order: where a later one is a call (or an allocation), lowered to a statement before the
        /// expression, each earlier one is evaluated into a temporary before it, so its checks (and its reads of
        /// memory) come first, as they do in C#.
        /// </summary>
        private KExpr[] Operands(params IOperation[] ops)
        {
            var values = new KExpr[ops.Length];
            var after = new int[ops.Length];
            for (int k = 0; k < ops.Length; k++)
            {
                values[k] = Expr(ops[k]);
                after[k] = _block.Stmts.Count;
            }
            int end = _block.Stmts.Count;
            for (int k = ops.Length - 2; k >= 0; k--)
            {
                if (after[k] == end || values[k] is KLit || values[k] is KVar || !InSubset(ops[k].Type)) continue;
                var t = Declare("t$" + _temps++, ops[k].Type);
                _block.Stmts.Insert(after[k], new KAssign { Var = t, Value = values[k] });
                values[k] = new KVar(t);
            }
            return values;
        }

        private KExpr Arith(string op, KExpr l, KExpr r, ITypeSymbol type, SyntaxNode at, bool isChecked)
        {
            // (x += y, x++ of floats: rounded, never an overflow)
            if (IsFloating(type) && op is "+" or "-" or "*" or "/")
            {
                KExpr F(KExpr x) => x is KLit lit && System.Numerics.BigInteger.TryParse(lit.Text, out var k) ? FloatLiteral((double)k, type) : x;
                return new KOp((op switch { "+" => "$fp.add", "-" => "$fp.sub", "*" => "$fp.mul", _ => "$fp.div" }) + FloatSize(type), F(l), F(r));
            }
            if (!IsIntegral(type)) throw new NotTranslated("arithmetic on " + type);
            var mode = Mode(at, isChecked);
            // (checked overflow, and MinValue / -1, throw an OverflowException: where exceptions are seen, to the handlers)
            var throwsTo = _cfgBlock != null && (mode == KMode.Checked || op is "/" or "%") && !_codeArith ? ThrowTarget(_cfgBlock.EnclosingRegion) : null;
            if (throwsTo != null) _p.ExceptionTypes.Add(_model.Compilation.GetTypeByMetadataName("System.OverflowException"));
            return new KArith { Op = op, Left = l, Right = r, Type = type, Mode = mode, At = at, ThrowsTo = throwsTo };
        }

        private static string Op(BinaryOperatorKind k) => k switch
        {
            BinaryOperatorKind.Add => "+", BinaryOperatorKind.Subtract => "-", BinaryOperatorKind.Multiply => "*",
            BinaryOperatorKind.Divide => "/", BinaryOperatorKind.Remainder => "%",
            _ => throw new NotTranslated("the operator " + k),
        };

        private KExpr Expr(IOperation e)
        {
            if (DataExpr(e, Expr, BindInCode) is KExpr data) return data;
            // (a cancellation token's state: cancelled may change at any moment, so each read is a value of its own; whether it
            // can be is fixed)
            if (e is IPropertyReferenceOperation tk && tk.Instance != null && IsToken(tk.Instance.Type) && tk.Property.Name == "CanBeCanceled")
                return new KOp("$canBeCanceled", Expr(tk.Instance));
            // (a lock's object read as a value, new Releaser(_s): some object, not null where declared so (no state of the kernel's))
            if (e is IFieldReferenceOperation lockRead && IsLockObject(lockRead.Field))
            {
                if (lockRead.Instance != null && !(lockRead.Instance is IInstanceReferenceOperation)) Expr(lockRead.Instance);
                var lt = Declare("t$" + _temps++, lockRead.Type);
                Emit(new KHavoc { Var = lt });
                if (NotNullable(lockRead.Field.Type)) Emit(new KAssume { Cond = new KOp("!=", new KVar(lt), new KLit("null")) });
                return new KVar(lt);
            }
            // (default(CancellationToken), CancellationToken.None: a token, of whatever state)
            if (e is IDefaultValueOperation dt && IsToken(dt.Type) || e is IPropertyReferenceOperation { Property.Name: "None", Instance: null } tn && IsToken(tn.Type))
            {
                var tt = Declare("t$" + _temps++, e.Type);
                Emit(new KHavoc { Var = tt });
                return new KVar(tt);
            }
            if (e is IPropertyReferenceOperation { Property.Name: "Result", Instance: ILocalReferenceOperation resultOf } && _tasks.TryGetValue(resultOf.Local, out var resultTask)) return ResultOf(resultTask, e.Syntax);
            // (EF's tracker: Database.CurrentTransaction, Entry(o).State)
            if (e is IPropertyReferenceOperation trackerRead && TrackerRead(trackerRead) is KExpr tracked) return tracked;
            // (a context's table, ctx.Orders or ctx.Set<T>(): a reference that changes nothing;
            // what reads it is Lowering.Ef's)
            if (KernelTypes.Ef != null && DbSetEntity(e.Type) != null &&
                (e is IPropertyReferenceOperation { Instance: { } dbi } && KernelTypes.Ef.IsContextType(dbi.Type) ||
                 e is IInvocationOperation { TargetMethod.Name: "Set", Instance: { } dbs, Arguments.Length: 0 } && KernelTypes.Ef.IsContextType(dbs.Type)))
            {
                var ctx = e is IPropertyReferenceOperation pdb ? pdb.Instance : ((IInvocationOperation)e).Instance;
                var cv = Expr(ctx);
                Emit(new KCheck { Cond = new KOp("!=", cv, new KLit("null")), Id = "CSV1013", At = ctx.Syntax, Message = $"'{ctx.Syntax}' might be null in '{e.Syntax}'" });
                var table = Declare("t$" + _temps++, e.Type);
                Emit(new KHavoc { Var = table });
                Emit(new KAssume { Cond = new KOp("!=", new KVar(table), new KLit("null")) });
                return new KVar(table);
            }
            // (a transaction as an object, compared with null: itself)
            if (e is IConversionOperation { IsImplicit: true, Conversion.IsReference: true } txc && IsEfTransaction(txc.Operand.Type)) return Expr(txc.Operand);
            switch (e)
            {
                case { ConstantValue: { HasValue: true } cv } when Scalar(e.Type) || IsFloating(e.Type) || IsNullable(e.Type): return Constant(cv.Value, e.Type);
                case ILocalReferenceOperation l when InSubset(l.Local.Type) && l.Local.RefKind == RefKind.None: return new KVar(Declare(Local(l.Local), l.Local.Type));
                case ILocalReferenceOperation rr when _refAlias.TryGetValue(rr.Local, out var ra):
                    if (ra.Var != null) return new KVar(ra.Var);
                    HeldCell(ra.Array, rr.Syntax, write: false);
                    return new KElem { Array = ra.Array, Index = ra.Index, ArrayType = ra.ArrayType, At = rr.Syntax, ArrayAt = rr.Syntax,
                                       Alongside = InSpec(rr.Syntax) ? null : Concurrent ? new KLit("true") : Running() };
                case IParameterReferenceOperation ap when _assigned.TryGetValue(ap.Parameter, out var apLocal): return new KVar(apLocal);
                // (a compiled query's lambda's, where it's called: its argument)
                case IParameterReferenceOperation cq when _compiledParams.Contains(cq.Parameter): return new KVar("q$" + cq.Parameter.Name);
                case IParameterReferenceOperation p when InSubset(p.Parameter.Type) && (p.Parameter.RefKind is RefKind.None or RefKind.Ref or RefKind.Out || p.Parameter.RefKind == RefKind.In && (IsMemView(p.Parameter.Type) || InValue(p.Parameter))):
                    return new KVar(Local(p.Parameter));
                // (Math.Max, Min and Abs of integers: Abs(MinValue) throws, as checked negation does)
                case IInvocationOperation im when IntegerMath(im):
                {
                    var v = Operands(im.Arguments.OrderBy(a => a.Parameter.Ordinal).Select(a => a.Value).ToArray());
                    return im.TargetMethod.Name == "Abs"
                        ? new KOp("ite", new KOp(">=", v[0], new KLit("0")), v[0], Arith("-", new KLit("0"), v[0], im.Type, im.Syntax, isChecked: true))
                        : MinMax(im.TargetMethod.Name, v[0], v[1]);
                }
                case IInvocationOperation own when SpecSymbols.IsCsVerifyType(own.TargetMethod.ContainingType, "Own"):
                    return Own(own);
                // (a quantifier in code, a [Pure] or ghost function's body: mathematics, its reads checked over its range)
                case IInvocationOperation q when SpecSymbols.IsSpecClass(q.TargetMethod.ContainingType) && q.TargetMethod.Name is "Forall" or "Exists" && q.Arguments.Length == 3:
                    // (read as the source has it: the graph lowers its lambda)
                    return Spec(_model.GetOperation(q.Syntax) as IInvocationOperation ?? q, null);
                case IInvocationOperation mv when mv.TargetMethod.Name == "MoveNext" && mv.Instance is IFlowCaptureReferenceOperation ev && _forEach.TryGetValue(ev.Id, out var fv) && fv.Version != null:
                {
                    // (the list may not have changed since: MoveNext throws if it has; whether there's another, unknown)
                    var what = CollectionKind(fv.Collection) switch { "Dictionary" => "dictionary", "HashSet" => "set", "Stack" => "stack", "Queue" => "queue", _ => "list" };
                    Emit(new KCheck { Cond = new KOp("==", new KOp("sel", new KVar(VersionMap), new KVar(fv.Array)), new KVar(fv.Version)), Id = "CSV1001", At = fv.At,
                                      Message = $"the {what} may have changed while it is enumerated: MoveNext would throw InvalidOperationException (collection was modified)" });
                    var more = Declare("t$" + _temps++, _model.Compilation.GetSpecialType(SpecialType.System_Boolean));
                    Emit(new KHavoc { Var = more });
                    // (it gives at most the Count it had where the loop began (a dictionary's Remove may go on while it's
                    // enumerated, the version as it was); all of them where the Count is still that)
                    if (fv.Size0 != null)
                    {
                        var (i, n0) = (new KVar(fv.Index), new KVar(fv.Size0));
                        Emit(new KAssume { Cond = new KOp("==>", new KVar(more), new KOp("<", i, n0)) });
                        Emit(new KAssume { Cond = new KOp("==>", new KOp("&&", new KOp("!", new KVar(more)), new KOp("==", LengthOf(fv), n0)), new KOp("==", i, n0)) });
                    }
                    return new KVar(more);
                }
                // (an enumerator the kernel doesn't look into: its MoveNext may run the program's code, which may change
                // anything; whether there's another isn't known)
                case IInvocationOperation om when om.TargetMethod.Name == "MoveNext" && om.Instance is IFlowCaptureReferenceOperation eo && _forEach.TryGetValue(eo.Id, out var fo) && fo.Opaque:
                {
                    CallersRun();
                    var more = Declare("t$" + _temps++, _model.Compilation.GetSpecialType(SpecialType.System_Boolean));
                    Emit(new KHavoc { Var = more });
                    return new KVar(more);
                }
                case IInvocationOperation mn when mn.TargetMethod.Name == "MoveNext" && mn.Instance is IFlowCaptureReferenceOperation er && _forEach.TryGetValue(er.Id, out var fm):
                    return new KOp("<", new KVar(fm.Index), LengthOf(fm));
                case IConversionOperation cc when Unconverted(cc) is IPropertyReferenceOperation { Property.Name: "Current", Instance: IFlowCaptureReferenceOperation cr } && _forEach.TryGetValue(cr.Id, out var fcur):
                {
                    var el = Current(fcur);
                    return SymbolEqualityComparer.Default.Equals(cc.Type, fcur.Element) ? el : new KConv { Value = el, From = fcur.Element, To = cc.Type, Mode = KMode.Default, At = cc.Syntax };
                }
                case IPropertyReferenceOperation { Property.Name: "Current", Instance: IFlowCaptureReferenceOperation cr2 } when _forEach.TryGetValue(cr2.Id, out var fcur2):
                    return Current(fcur2);
                // (an enumerator's Current: an element, not known which)
                case IPropertyReferenceOperation { Property.Name: "Current", Instance: ILocalReferenceOperation { Local: var ecl } } ecur when _enumerators.ContainsKey(ecl) && InSubset(ecur.Type):
                {
                    var v = Declare("t$" + _temps++, ecur.Type);
                    Emit(new KHavoc { Var = v });
                    return new KVar(v);
                }
                case IPropertyReferenceOperation { Property.Name: "Current", Instance: IFlowCaptureReferenceOperation ac } when _asyncEach.TryGetValue(ac.Id, out var acur):
                {
                    var v = Declare("t$" + _temps++, acur.Element);
                    Emit(new KHavoc { Var = v });
                    if (IsNullable(acur.Element) && NotNullable(acur.Element)) Emit(new KAssume { Cond = new KOp("!=", new KVar(v), new KLit("null")) });
                    return new KVar(v);
                }
                case IFlowCaptureReferenceOperation r: return new KVar(Capture(r.Id, r.Type));
                case IInstanceReferenceOperation { ReferenceKind: InstanceReferenceKind.ContainingTypeInstance } when !_p.IsCtor:
                    return new KVar("this");
                // (in a catch: the exception it caught)
                case ICaughtExceptionOperation _:
                    return new KVar("ex$");
                // (a new exception of the library's: its arguments' values aren't kept, only what is in the kernel is checked)
                // (a list: its stub's constructor, which gives a new one)
                case IObjectCreationOperation lo when IsCollection(lo.Type) && lo.Initializer == null && lo.Constructor != null:
                    return Invoke(lo.Constructor, null, lo.Arguments, lo.Syntax, null);
                // (a struct's constructor: the value it gives)
                case IObjectCreationOperation sc when IsStruct(sc.Type) && sc.Initializer == null && sc.Constructor != null && !sc.Constructor.IsImplicitlyDeclared:
                    return Invoke(sc.Constructor, null, sc.Arguments, sc.Syntax, null);
                case IObjectCreationOperation ne when IsException(ne.Type) && !IsClass(ne.Type) && ne.Initializer == null:
                {
                    foreach (var a in ne.Arguments.Where(a => InSubset(a.Value.Type) && !(a.Value is IInterpolatedStringOperation))) Expr(a.Value);
                    var t = Declare("t$" + _temps++, ne.Type);
                    _p.ExceptionTypes.Add(ne.Type);
                    Emit(new KNewExc { Var = t, Type = ne.Type });
                    return new KVar(t);
                }
                // (this, in a constructor, as a value: it escapes before the object is built. Where the class has invariants or
                // non-nullable fields, CSV1015; the object goes on, as it is)
                case IInstanceReferenceOperation ti when _p.IsCtor && ti.ReferenceKind == InstanceReferenceKind.ContainingTypeInstance:
                {
                    var type = _m.ContainingType;
                    bool invariants = HasObjectInvariant(type);
                    if (invariants || InstanceFields(type).Any(f => IsNullable(FieldType(f)) && NotNullable(FieldType(f))))
                        Emit(new KCheck { Cond = new KLit("false"), Id = "CSV1015", At = ti.Syntax, NotAssumedAfter = true,
                                          Message = invariants ? $"'this' escapes the constructor of {type.Name} before its invariant is established"
                                                               : $"'this' escapes the constructor of {type.Name}, whose non-nullable fields may not be set yet" });
                    return new KVar("this");
                }
                case IInstanceReferenceOperation _:
                    throw new NotTranslated(_p.IsCtor ? "this, escaping its constructor" : "an instance reference");
                // (a computed property: its getter, called)
                case IPropertyReferenceOperation cp when IsComputed(cp.Property) && cp.Property.GetMethod != null:
                    return Invoke(cp.Property.GetMethod, cp.Instance, cp.Arguments, cp.Syntax, null);
                // (a dictionary's Keys.Count or Values.Count: its Count)
                case IPropertyReferenceOperation { Property.Name: "Count", Instance: IPropertyReferenceOperation { Property.Name: "Keys" or "Values", Instance: { } vd } } when CollectionKind(vd.Type) == "Dictionary" && IsCollection(vd.Type):
                    return Invoke(((INamedTypeSymbol)vd.Type).GetMembers("Count").OfType<IPropertySymbol>().First().GetMethod, vd, new IArgumentOperation[0], e.Syntax, null);
                // (a library property without a stub, Console.Out or a stream's Position: in code, each read a value of its own,
                // of its declared type, which warns but where it's shared state anyway)
                case IPropertyReferenceOperation lp when LibraryProperty(lp):
                {
                    if (lp.Instance != null)
                    {
                        var iv = Expr(lp.Instance);
                        if (IsNullable(lp.Instance.Type) && !(lp.Instance is IInstanceReferenceOperation))
                            Emit(new KCheck { Cond = new KOp("!=", iv, new KLit("null")), Id = "CSV1013", At = lp.Syntax, Message = $"'{lp.Instance.Syntax}' might be null in '{lp.Syntax}'" });
                    }
                    foreach (var a in lp.Arguments) Expr(a.Value);
                    var prop = lp.Property;
                    var ns = prop.ContainingType.ContainingNamespace?.ToDisplayString();
                    bool shared = prop.ContainingType.IsValueType && ns is "System.Threading" or "System.Threading.Tasks" or "System.Runtime.CompilerServices";
                    var span = lp.Syntax.GetLocation().GetLineSpan();
                    // (nor of one with a stub, a [Pure] one that says nothing more: Channel.Writer, a token source's Token)
                    bool stubbed = _contractOf?.Invoke(prop.GetMethod.OriginalDefinition) is Contract sc && sc.IsStub;
                    if (!shared && !stubbed && !(prop.Name == "Current" && prop.ContainingType.Name == "IAsyncEnumerator") && !_p.Warnings.Any(w => w.Span.Equals(span)))
                        _p.Warnings.Add(new VerificationDiagnostic("CSV1900", false, $"property '{prop.Name}' of {prop.ContainingType.Name} is not modeled; its value is unknown", span));
                    if (_p.Result != null) lock (_p.Result.LibraryCalls) _p.Result.LibraryCalls.Add((prop.OriginalDefinition.ToDisplayString(), lp.Syntax.SyntaxTree.FilePath + ":" + lp.Syntax.SpanStart));
                    var lv = Declare("t$" + _temps++, lp.Type);
                    Emit(new KHavoc { Var = lv });
                    if (IsNullable(lp.Type) && NotNullable(prop.OriginalDefinition.Type)) Emit(new KAssume { Cond = new KOp("!=", new KVar(lv), new KLit("null")) });
                    return new KVar(lv);
                }
                // (a static readonly field the kernel doesn't have: a value that never changes, not known which; not null
                // where its type says so)
                case IFieldReferenceOperation { Field: { IsStatic: true, IsReadOnly: true } srr } when StaticReadonly(srr) is KExpr srv:
                {
                    if (IsNullable(srr.Type) && NotNullable(srr.Type)) Emit(new KAssume { Cond = new KOp("!=", srv, new KLit("null")) });
                    if (IsIntegral(srr.Type)) Emit(new KAssume { Cond = InRange(srv, srr.Type) });
                    return srv;
                }
                case IFieldReferenceOperation _:
                case IPropertyReferenceOperation pf when !(pf.Property.Name == "Length" && IsArray(ActualArray(pf.Instance?.Type))) && !IsString(pf.Instance?.Type) && CollectionOf(pf.Instance?.Type) == null && !IsPair(pf.Instance?.Type) && !SpecSymbols.IsCsVerifyType(pf.Instance?.Type, "Seq`1") &&
                                                      !SpecSymbols.IsCsVerifyType(pf.Instance?.Type, "Ghost`1") && !SpecSymbols.IsCsVerifyType(pf.Instance?.Type, "Map`2") && !IsCollectionInterface(pf.Property.ContainingType) && !IsMemValue(pf.Instance?.Type) && !IsGivenTask(pf.Instance?.Type):
                {
                    var (field, instance, onThis, instanceAt) = FieldOf(e);
                    if (Atomics.IsAtomic(field) && !(_p.IsCtor && onThis)) return AtomicRead(field, instance, onThis, e.Syntax);
                    if (KernelTypes.Trees && SpecSymbols.IsOwnsField(field) && instance != null)
                    {
                        // (what an [Owns] field holds is in its container's tree, and isn't its root: it's owned)
                        var t = Declare("t$" + _temps++, FieldType(field));
                        Emit(new KAssign { Var = t, Value = new KField { Field = field, Instance = instance, OnThis = onThis, At = e.Syntax, InstanceAt = instanceAt } });
                        var r = new KVar("$root");
                        Emit(new KAssume { Cond = new KOp("||", new KOp("==", new KVar(t), new KLit("null")),
                            new KOp("&&", new KOp("==", new KOp("sel", r, new KVar(t)), new KOp("sel", r, instance)), new KOp("!=", new KOp("sel", r, new KVar(t)), new KVar(t)))) });
                        return new KVar(t);
                    }
                    return Unbox(new KField { Field = field, Instance = instance, OnThis = onThis, At = e.Syntax, InstanceAt = instanceAt }, FieldType(field), e.Type);
                }
                // (a library object: a new reference, of no fields of the program's; its constructor's arguments read)
                // (new string(c, n), new string(chars): a string of the library's, not null, of what length its arguments say where they do)
                case IObjectCreationOperation ns when IsString(ns.Type) && ns.Initializer == null && ns.Constructor != null && ns.Arguments.All(x => InSubset(x.Value.Type) && x.Parameter.RefKind == RefKind.None):
                {
                    var vs = ns.Arguments.OrderBy(x => x.Parameter.Ordinal).Select(x => Operand(x.Value, Expr, false)).ToList();
                    var t = Declare("t$" + _temps++, ns.Type);
                    Emit(new KHavoc { Var = t });
                    Emit(new KAssume { Cond = new KOp("!=", new KVar(t), new KLit("null")) });
                    if (ns.Arguments.Length == 2 && IsIntegral(ns.Arguments[1].Value.Type) && ns.Arguments[0].Value.Type?.SpecialType == SpecialType.System_Char)
                    {
                        Emit(new KCheck { Cond = new KOp(">=", vs[1], new KLit("0")), Id = "CSV1001", At = ns.Syntax, Message = $"'{ns.Syntax}' might throw: its count might be negative" });
                        Emit(new KAssume { Cond = new KOp("==", new KOp("slen", new KVar(t)), vs[1]) });
                    }
                    return new KVar(t);
                }
                case IObjectCreationOperation lob when (IsLibraryObject(lob.Type) || lob.Type.SpecialType == SpecialType.System_Object) && lob.Initializer == null && lob.Constructor != null &&
                                                       lob.Arguments.All(x => InSubset(x.Value.Type) && x.Parameter.RefKind == RefKind.None && (x.Value.Type?.TypeKind != TypeKind.Delegate || IsFunc(x.Parameter.Type))):
                {
                    foreach (var x in lob.Arguments.OrderBy(x => x.Parameter.Ordinal))
                    {
                        var xv = Expr(x.Value);
                        if (IsFunc(x.Parameter.Type)) StoredInLibrary(lob.Constructor, x, xv);
                    }
                    var t = Declare("t$" + _temps++, lob.Type);
                    Emit(new KNewObj { Var = t, Type = lob.Type, Ctor = null, Args = new KExpr[0], ArgsAt = new SyntaxNode[0], At = lob.Syntax });
                    return new KVar(t);
                }
                case IObjectCreationOperation oc when IsClass(oc.Type) && oc.Initializer == null && oc.Constructor != null:
                {
                    var ctor = oc.Constructor.OriginalDefinition;
                    bool isImplicit = ctor.IsImplicitlyDeclared;
                    if (!isImplicit && !_isProcedure(ctor)) throw new NotTranslated("a call of " + oc.Type.Name + "'s constructor");
                    if (!isImplicit) _p.Calls.Add(ctor);
                    var ordered = oc.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
                    var args = Operands(ordered.Select(a => a.Value).ToArray());
                    // (a generic class's constructor takes boxes for its T: new Box<int>(3))
                    for (int k = 0; k < args.Length; k++) args[k] = Box(args[k], ctor.Parameters[ordered[k].Parameter.Ordinal].Type, ordered[k].Parameter.Type);
                    var t = Declare("t$" + _temps++, oc.Type);
                    foreach (var f in InstanceFields(oc.Type)) _p.Fields.Add(f);
                    Emit(new KNewObj { Var = t, Type = oc.Type, Ctor = isImplicit ? null : ctor, Args = args, ArgsAt = ordered.Select(a => a.Value.Syntax).ToArray(), At = oc.Syntax });
                    // (exactly a C)
                    if (IsModeledClass(oc.Type))
                    {
                        _p.ClassTypes.Add(oc.Type.OriginalDefinition);
                        Emit(new KAssume { Cond = new KOp("==", new KOp("dtype", new KVar(t)), new KLit(TypeConst(oc.Type))) });
                    }
                    // (a context made: it tracks nothing, and has nothing open)
                    if (IsContext(oc.Type)) NewContext(new KVar(t));
                    return new KVar(t);
                }
                case IParenthesizedOperation par: return Expr(par.Operand);
                // (object.ReferenceEquals(a, b): == of the two objects)
                case IInvocationOperation re when re.TargetMethod is { Name: "ReferenceEquals", IsStatic: true, ContainingType.SpecialType: SpecialType.System_Object } && re.Arguments.Length == 2 &&
                                                  re.Arguments.All(a => InSubset(a.Value.Type)):
                {
                    var ordered = re.Arguments.OrderBy(a => a.Parameter.Ordinal).ToList();
                    var a0 = Declare("t$" + _temps++, ordered[0].Value.Type);
                    Emit(new KAssign { Var = a0, Value = Expr(ordered[0].Value) });
                    return new KOp("==", new KVar(a0), Expr(ordered[1].Value));
                }
                // (an assignment as an expression, (x = 10) > 5: written, then its value)
                case ISimpleAssignmentOperation sa when !sa.IsRef && InSubset(sa.Type) && sa.Target is ILocalReferenceOperation or IParameterReferenceOperation or IFieldReferenceOperation or IArrayElementReferenceOperation:
                {
                    var t = Declare("t$" + _temps++, sa.Type);
                    Emit(new KAssign { Var = t, Value = Expr(sa.Value) });
                    Assign(sa.Target, new KVar(t));
                    return new KVar(t);
                }
                case IConversionOperation conv when conv.Conversion.IsIdentity || conv.IsImplicit && IsIntegral(conv.Type) && IsIntegral(conv.Operand.Type) && conv.Conversion.IsNumeric:
                    return Expr(conv.Operand);
                // (a data value as an object: an object of its own, which no other is known to be, though they be equal values)
                case IConversionOperation dobj when dobj.IsImplicit && IsData(dobj.Operand.Type) && dobj.Type.SpecialType == SpecialType.System_Object:
                {
                    Expr(dobj.Operand);
                    var t = Declare("t$" + _temps++, dobj.Type);
                    Emit(new KHavoc { Var = t });
                    Emit(new KAssume { Cond = new KOp("!=", new KVar(t), new KLit("null")) });
                    return new KVar(t);
                }
                // (an array or a modeled collection as a collection interface: what it is goes with it)
                case IConversionOperation ci when ci.IsImplicit && IsCollectionInterface(ci.Type) && (IsArray(ci.Operand.Type) || IsCollection(ci.Operand.Type)):
                {
                    var t = Declare("t$" + _temps++, ci.Type);
                    Emit(new KAssign { Var = t, Value = Expr(ci.Operand) });
                    Emit(new KAssume { Cond = new KOp("||", new KOp("==", new KVar(t), new KLit("null")), new KOp(IsArray(ci.Operand.Type) ? "$arr" : "$coll", new KVar(t))) });
                    return new KVar(t);
                }
                case IPropertyReferenceOperation ir when ir.Instance != null && IsCollectionInterface(ir.Property.ContainingType) &&
                                                         (ir.Property.Name == "Count" && ir.Arguments.Length == 0 || ir.Property.IsIndexer && ir.Arguments.Length == 1):
                    return Ifc(ir, ir.Property.IsIndexer ? Expr(ir.Arguments[0].Value) : null, Expr(ir.Instance), inSpec: false);
                case IConversionOperation conv when Upcast(conv):
                    return conv.Operand.ConstantValue.HasValue ? new KLit("null") : Expr(conv.Operand);
                // (a target-typed conditional, Sh s = c ? new S1() : new S2(): each branch already converted)
                case IConversionOperation tt when tt.IsImplicit && tt.OperatorMethod == null && SymbolEqualityComparer.Default.Equals(tt.Type, tt.Operand.Type):
                    return Expr(tt.Operand);
                // (and an enum's: an integer of its underlying type)
                case IConversionOperation conv when IsIntegral(conv.Type) && IsIntegral(conv.Operand.Type) && (conv.Conversion.IsNumeric || conv.Type.TypeKind == TypeKind.Enum || conv.Operand.Type.TypeKind == TypeKind.Enum):
                    return new KConv { Value = Expr(conv.Operand), From = conv.Operand.Type, To = conv.Type, Mode = Mode(conv.Syntax, conv.IsChecked), At = conv.Syntax };
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Not: return new KOp("!", Expr(u.Operand));
                case IUnaryOperation bn when bn.OperatorKind == UnaryOperatorKind.BitwiseNegation && IsIntegral(bn.Type): return Complement(Expr(bn.Operand), bn.Type);
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Plus: return Expr(u.Operand);
                case IUnaryOperation u when u.OperatorKind == UnaryOperatorKind.Minus && IsIntegral(u.Type):
                    return Arith("-", new KLit("0"), Expr(u.Operand), u.Type, u.Syntax, u.IsChecked);
                case IBinaryOperation b when b.OperatorMethod == null && !(IsString(b.Type) && b.OperatorKind == BinaryOperatorKind.Add) && (InSubset(b.LeftOperand.Type) && InSubset(b.RightOperand.Type) ||
                                             b.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals && (RefOperand(b.LeftOperand) || RefOperand(b.RightOperand))):
                    return Binary(b);
                case IArrayElementReferenceOperation el when IsArray(el.ArrayReference.Type) && el.Indices.Length == 1:
                {
                    var v = Operands(el.ArrayReference, el.Indices[0]);
                    HeldCell(v[0], el.Syntax, write: false);
                    return new KElem { Array = v[0], Index = v[1], ArrayType = el.ArrayReference.Type, At = el.Syntax, ArrayAt = el.ArrayReference.Syntax,
                                       Alongside = InSpec(el.Syntax) ? null : Concurrent ? new KLit("true") : Running() };
                }
                case IPropertyReferenceOperation { Property.Name: "Result", Instance: ILocalReferenceOperation rl } when _tasks.TryGetValue(rl.Local, out var rt):
                    return ResultOf(rt, e.Syntax);
                // (a list's Count and indexer: its stub's getters)
                case IPropertyReferenceOperation kp when IsPair(kp.Instance?.Type) && kp.Property.Name is "Key" or "Value":
                    return Pair(Expr(kp.Instance), kp.Instance.Type, kp.Property.Name);
                // (a given task's Result: a value not known)
                case IPropertyReferenceOperation { Property.Name: "Result" } tr when tr.Instance != null && IsGivenTask(tr.Instance.Type) && InSubset(tr.Type):
                {
                    Expr(tr.Instance);
                    var r = Declare("t$" + _temps++, tr.Type);
                    Emit(new KHavoc { Var = r });
                    return new KVar(r);
                }
                case IPropertyReferenceOperation lp when IsCollection(lp.Instance?.Type) && lp.Property.GetMethod != null:
                    return Invoke(lp.Property.GetMethod, lp.Instance, lp.Arguments, lp.Syntax, null);
                case IPropertyReferenceOperation sl when sl.Property.Name == "Length" && IsString(sl.Instance?.Type):
                    return new KLen { String = true, Array = Expr(sl.Instance), At = sl.Syntax, ArrayAt = sl.Instance.Syntax };
                case IPropertyReferenceOperation sc when sc.Property.IsIndexer && IsString(sc.Instance?.Type) && sc.Arguments.Length == 1:
                {
                    var v = Operands(sc.Instance, sc.Arguments[0].Value);
                    return new KElem { String = true, Array = v[0], Index = v[1], At = sc.Syntax, ArrayAt = sc.Instance.Syntax };
                }
                // ((T[])a.Clone(): a new array of a's length, its elements a's)
                case IConversionOperation { Operand: IInvocationOperation { TargetMethod.Name: "Clone", Arguments.Length: 0, Instance: { } ci } } cc
                    when IsArray(cc.Type) && IsArray(ci.Type) && SymbolEqualityComparer.Default.Equals(cc.Type, ci.Type) && !_p.MemViews:
                {
                    var src = Expr(ci);
                    Emit(new KCheck { Cond = new KOp("!=", src, new KLit("null")), Id = "CSV1013", At = ci.Syntax, Message = $"'{ci.Syntax}' might be null in '{cc.Operand.Syntax}'" });
                    return CopyOf(src, new KLit("0"), new KOp("len", src), cc.Type, cc.Syntax);
                }
                // (n++ and ++n as values: stored, as a statement stores it; the value before, or after)
                case IIncrementOrDecrementOperation iv when IsIntegral(iv.Type):
                {
                    var before = Declare("t$" + _temps++, iv.Type);
                    Emit(new KAssign { Var = before, Value = Expr(iv.Target) });
                    var after = Declare("t$" + _temps++, iv.Type);
                    Emit(new KAssign { Var = after, Value = Arith(iv.Kind == OperationKind.Increment ? "+" : "-", new KVar(before), new KLit("1"), iv.Type, iv.Syntax, iv.IsChecked) });
                    Assign(iv.Target, new KVar(after));
                    return new KVar(iv.IsPostfix ? before : after);
                }
                // (a string + something else, "line " + n: the other's text, ToString's, is a string not known)
                case IBinaryOperation so when so.OperatorKind == BinaryOperatorKind.Add && IsString(so.Type) &&
                                              IsString(Unconverted(so.LeftOperand).Type) != IsString(Unconverted(so.RightOperand).Type):
                {
                    var stringLeft = IsString(Unconverted(so.LeftOperand).Type);
                    var str = Expr(stringLeft ? so.LeftOperand : so.RightOperand);
                    var other = Unconverted(stringLeft ? so.RightOperand : so.LeftOperand);
                    if (!InSubset(other.Type)) throw new NotTranslated("a string + " + other.Type);
                    Expr(other);
                    var text = Declare("t$" + _temps++, so.Type);
                    Emit(new KHavoc { Var = text });
                    Emit(new KAssume { Cond = new KOp("!=", new KVar(text), new KLit("null")) });
                    return stringLeft ? StringBinary(BinaryOperatorKind.Add, str, new KVar(text)) : StringBinary(BinaryOperatorKind.Add, new KVar(text), str);
                }
                case IBinaryOperation sb when IsString(sb.LeftOperand.Type) && IsString(sb.RightOperand.Type) &&
                                             (sb.OperatorMethod == null || IsString(sb.OperatorMethod.ContainingType)) &&
                                             sb.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals or BinaryOperatorKind.Add:
                {
                    var v = Operands(sb.LeftOperand, sb.RightOperand);
                    return RelationalStrings(sb, StringBinary(sb.OperatorKind, v[0], v[1]), v[0], v[1]);
                }
                case IPropertyReferenceOperation pr when pr.Property.Name == "Length" && IsArray(ActualArray(pr.Instance?.Type)):
                    return new KLen { Array = Expr(pr.Instance), At = pr.Syntax, ArrayAt = pr.Instance.Syntax };
                // (a rectangular array: each size not negative (CSV1003), its lengths, and its initializer's cells)
                case IArrayCreationOperation mc when IsMultiArray(mc.Type) && mc.DimensionSizes.Length == ((IArrayTypeSymbol)mc.Type).Rank:
                {
                    var sizes = Operands(mc.DimensionSizes.ToArray());
                    foreach (var s in sizes)
                        Emit(new KCheck { Cond = new KOp("<=", new KLit("0"), s), Id = "CSV1003", At = mc.Syntax, Message = $"array size in '{mc.Syntax}' might be negative" });
                    var t = Declare("t$" + _temps++, mc.Type);
                    Emit(new KNew { Var = t, ArrayType = mc.Type, Size = sizes.Skip(1).Aggregate(sizes[0], (x, y) => new KOp("*", x, y)) });
                    for (int d = 0; d < sizes.Length; d++) Emit(new KAssume { Cond = new KOp("==", new KOp("$dim", new KVar(t), new KLit(d.ToString())), sizes[d]) });
                    void Fill(IArrayInitializerOperation init, List<KExpr> prefix)
                    {
                        for (int i = 0; i < init.ElementValues.Length; i++)
                        {
                            var at = new List<KExpr>(prefix) { new KLit(i.ToString()) };
                            if (at.Count < sizes.Length) Fill((IArrayInitializerOperation)init.ElementValues[i], at);
                            else Emit(new KStore { Unchecked = true, Array = new KVar(t), Index = CellOf(at), Value = Expr(init.ElementValues[i]), ArrayType = mc.Type, At = mc.Syntax, ArrayAt = mc.Syntax });
                        }
                    }
                    if (mc.Initializer != null) Fill(mc.Initializer, new List<KExpr>());
                    return new KVar(t);
                }
                case IArrayCreationOperation ac when IsArray(ac.Type) && ac.DimensionSizes.Length == 1:
                {
                    var v = Operands(new[] { ac.DimensionSizes[0] }.Concat(ac.Initializer?.ElementValues ?? Enumerable.Empty<IOperation>()).ToArray());
                    var size = v[0];
                    var elements = ac.Initializer == null ? null : v.Skip(1).ToArray();
                    var t = Declare("t$" + _temps++, ac.Type);
                    Emit(new KNew { Var = t, ArrayType = ac.Type, Size = size, Elements = elements });
                    return new KVar(t);
                }
                case IInvocationOperation call:
                    return Call(call);
                case IAwaitOperation aw:
                    return Await(aw) ?? throw new NotTranslated("an await of nothing, as a value");
                case IIsNullOperation isNull:
                    return new KOp("==", Expr(Unconverted(isNull.Operand)), new KLit("null"));
                // (a method group made a delegate of a contract: its contract isn't compared with the type's, CSV1029;
                // the delegate a new reference, its code not known)
                case IDelegateCreationOperation cg when Contracted(cg.Type) && cg.Target is IMethodReferenceOperation cgm:
                {
                    var receiver = cgm.Instance != null && !(cgm.Instance is IInstanceReferenceOperation) ? Expr(cgm.Instance) : null;
                    // (its contract against the delegate type's, behavioural subtyping: it accepts all the type does, and
                    // gives what the type says where the type's precondition holds)
                    if (Refines(cgm.Method, ((INamedTypeSymbol)cg.Type).DelegateInvokeMethod, receiver) is (KExpr accepts, KExpr gives))
                    {
                        Emit(new KCheck { Cond = accepts, Id = "CSV1029", At = cg.Syntax, NotAssumedAfter = true,
                                          Message = $"'{cgm.Method.Name}' made a '{cg.Type.Name}': its precondition might not accept every argument the delegate type's does" });
                        Emit(new KCheck { Cond = gives, Id = "CSV1029", At = cg.Syntax, NotAssumedAfter = true,
                                          Message = $"'{cgm.Method.Name}' made a '{cg.Type.Name}': its postcondition might not give what the delegate type's says" });
                    }
                    else
                        Emit(new KCheck { Cond = new KLit("false"), Id = "CSV1029", At = cg.Syntax, NotAssumedAfter = true,
                                          Message = $"'{cgm.Method.Name}' made a '{cg.Type.Name}': its contract, or the delegate type's, depends on state, so it isn't known to keep the type's (use a lambda)" });
                    var t = Declare("t$" + _temps++, cg.Type);
                    Emit(new KHavoc { Var = t });
                    Emit(new KAssume { Cond = new KOp("!=", new KVar(t), new KLit("null")) });
                    return new KVar(t);
                }
                case IDelegateCreationOperation cd when Contracted(cd.Type) && LambdaOf(cd.Target) != null:
                {
                    // (a lambda made a delegate with a contract: proved against it on its own; here, a new reference)
                    var t = Declare("t$" + _temps++, cd.Type);
                    Emit(new KNewObj { Var = t, Type = cd.Type, At = cd.Syntax, Args = new KExpr[0], ArgsAt = new SyntaxNode[0] });
                    return new KVar(t);
                }
                case IDelegateCreationOperation dc when IsFunc(dc.Type) && LambdaOf(dc.Target) is IAnonymousFunctionOperation af:
                    return Lambda(dc, af);
                case IDelegateCreationOperation mg when IsFunc(mg.Type) && mg.Target is IMethodReferenceOperation mr &&
                                                       (!mr.Method.IsGenericMethod || mr.Method.IsStatic && mr.Method.OriginalDefinition.TypeParameters.All(IsGenericParameter) &&
                                                        mr.Method.OriginalDefinition.TypeParameters.Zip(mr.Method.TypeArguments).All(x => Instantiates(x.First, x.Second))) &&
                                                       (mr.Method.IsStatic || mr.Instance != null && IsRef(mr.Instance.Type)) &&
                                                       !SymbolEqualityComparer.Default.Equals(mr.Method.OriginalDefinition, _m.OriginalDefinition):
                    return MethodGroup(mg, mr.Method, mr.Method.IsStatic ? null : mr.Instance);
                // ($"...{x}...": its holes evaluated, in order, as they'd throw; a string, not null, of contents not known)
                case IInterpolatedStringOperation istr:
                {
                    foreach (var part in istr.Parts.OfType<IInterpolationOperation>())
                    {
                        if (!InSubset(part.Expression.Type) && !(Unconverted(part.Expression) is var u && InSubset(u.Type)))
                            throw new NotTranslated("a hole of " + part.Expression.Type);
                        // (read into a variable: its checks are where it's read)
                        var hole = InSubset(part.Expression.Type) ? part.Expression : Unconverted(part.Expression);
                        Emit(new KAssign { Var = Declare("t$" + _temps++, hole.Type), Value = Expr(hole) });
                        if (part.Alignment != null) Expr(part.Alignment);
                    }
                    var str = Declare("t$" + _temps++, istr.Type);
                    Emit(new KHavoc { Var = str });
                    Emit(new KAssume { Cond = new KOp("!=", new KVar(str), new KLit("null")) });
                    return new KVar(str);
                }
                // (anonymous objects compared as objects: their references, not known (the kernel's values are one per contents))
                case IBinaryOperation ac when ac.OperatorKind is BinaryOperatorKind.Equals or BinaryOperatorKind.NotEquals && AnonymousAsObject(ac.LeftOperand) && AnonymousAsObject(ac.RightOperand):
                {
                    Expr(Unconverted(ac.LeftOperand));
                    Expr(Unconverted(ac.RightOperand));
                    var same = Declare("t$" + _temps++, ac.Type);
                    Emit(new KHavoc { Var = same });
                    return new KVar(same);
                }
                // (a library value the kernel doesn't look into, new TimeSpan(...), new DateTime(...): its arguments read, its value not known)
                case IObjectCreationOperation ov when IsOpaqueValue(ov.Type) && ov.Initializer == null && ov.Arguments.All(a => a.Parameter.RefKind == RefKind.None && InSubset(a.Value.Type)):
                {
                    foreach (var a in ov.Arguments.OrderBy(a => a.Parameter.Ordinal)) Emit(new KAssign { Var = Declare("t$" + _temps++, a.Value.Type), Value = Expr(a.Value) });
                    var made = Declare("t$" + _temps++, ov.Type);
                    Emit(new KHavoc { Var = made });
                    return new KVar(made);
                }
                // (a value boxed, as object or an interface it has: an object of its own, not null, which no other is known to be)
                case IConversionOperation bx when bx.IsImplicit && bx.Operand.Type?.IsValueType == true && !bx.Type.IsValueType && InSubset(bx.Operand.Type) && TypeOf(bx.Type) == "Ref":
                {
                    Emit(new KAssign { Var = Declare("t$" + _temps++, bx.Operand.Type), Value = Expr(bx.Operand) });
                    var boxed = Declare("t$" + _temps++, bx.Type);
                    Emit(new KHavoc { Var = boxed });
                    Emit(new KAssume { Cond = new KOp("!=", new KVar(boxed), new KLit("null")) });
                    return new KVar(boxed);
                }
                // (a task, or a library's object, as object or an interface it has: the same reference)
                case IConversionOperation tr when tr.IsImplicit && tr.Conversion.IsReference && (IsGivenTask(tr.Operand.Type) || IsLibraryObject(tr.Operand.Type) ||
                                                  IsSequence(tr.Type) && (IsCollection(tr.Operand.Type) || IsArray(tr.Operand.Type))) && TypeOf(tr.Type) == "Ref":
                    return Expr(tr.Operand);
                default:
                    if (e.ConstantValue.HasValue && e.ConstantValue.Value == null && IsNullable(e.Type)) return new KLit("null");
                    throw new NotTranslated(e.Kind + " '" + e.Syntax + "'");
            }
        }

        /// <summary>
        /// A reference made an object (to compare it with ==, or null): the same reference. Comparing two objects as
        /// objects is reference equality.
        /// </summary>
        private static bool Upcast(IConversionOperation conv) =>
            conv.IsImplicit && conv.Conversion.IsReference && (IsRef(conv.Operand.Type) || IsException(conv.Operand.Type) && (IsException(conv.Type) || conv.Type.SpecialType == SpecialType.System_Object) ||
                                                               IsGivenTask(conv.Operand.Type) && conv.Type.SpecialType == SpecialType.System_Object || conv.Operand.ConstantValue is { HasValue: true, Value: null }) ||
            // (a type parameter whose values are references, to object: C# calls it boxing, as T might be a struct; here it can't)
            conv.IsImplicit && conv.OperatorMethod == null && IsRefParameter(conv.Operand.Type) && conv.Type.SpecialType == SpecialType.System_Object;

        private static bool RefOperand(IOperation op) => IsRef(op.Type) || op is IConversionOperation c && Upcast(c) && IsRef(c.Operand.Type);

        private KExpr Constant(object v, ITypeSymbol type)
        {
            if (v is float or double && IsFloating(type)) return FloatLiteral(v, type);
            if (v is bool x) return new KLit(x ? "true" : "false");
            if (v == null && IsNullable(type)) return new KLit("null");
            // (a string literal: one value per contents)
            if (v is string str) return new KVar(_literal?.Invoke(str) ?? throw new NotTranslated("a string literal"));
            System.Numerics.BigInteger n;
            switch (v)
            {
                case char c: n = c; break;
                case sbyte b: n = b; break; case byte b: n = b; break;
                case short h: n = h; break; case ushort h: n = h; break;
                case int i: n = i; break; case uint i: n = i; break;
                case long l: n = l; break; case ulong l: n = l; break;
                default: throw new NotTranslated("a constant " + v);
            }
            return Number(n);
        }

        private KExpr Binary(IBinaryOperation b)
        {
            var v = Operands(b.LeftOperand, b.RightOperand);
            var (l, r) = (v[0], v[1]);
            switch (b.OperatorKind)
            {
                case BinaryOperatorKind.Add: case BinaryOperatorKind.Subtract: case BinaryOperatorKind.Multiply:
                case BinaryOperatorKind.Divide: case BinaryOperatorKind.Remainder:
                    return Arith(Op(b.OperatorKind), l, r, b.Type, b.Syntax, b.IsChecked);
                case var bk when IsBitwise(bk) && IsIntegral(b.Type):
                    return Bitwise(bk, l, r, b.Type, inSpec: false);
                case BinaryOperatorKind.Equals: return new KOp("==", l, r);
                case BinaryOperatorKind.NotEquals: return new KOp("!=", l, r);
                case BinaryOperatorKind.LessThan: return new KOp("<", l, r);
                case BinaryOperatorKind.LessThanOrEqual: return new KOp("<=", l, r);
                case BinaryOperatorKind.GreaterThan: return new KOp(">", l, r);
                case BinaryOperatorKind.GreaterThanOrEqual: return new KOp(">=", l, r);
                case BinaryOperatorKind.And when b.Type.SpecialType == SpecialType.System_Boolean:
                case BinaryOperatorKind.ConditionalAnd: return new KOp("&&", l, r);
                case BinaryOperatorKind.Or when b.Type.SpecialType == SpecialType.System_Boolean:
                case BinaryOperatorKind.ConditionalOr: return new KOp("||", l, r);
                case BinaryOperatorKind.ExclusiveOr when b.Type.SpecialType == SpecialType.System_Boolean: return new KOp("!=", l, r);
                default: throw new NotTranslated("the operator " + b.OperatorKind);
            }
        }

        /// <summary>== != and + of strings: equality of values (characters), and concatenation (null counts as empty).</summary>
        /// <summary>== and != of strings (in a lambda the database evaluates, by its collation: Lowering.Ef), and +.</summary>
        private KExpr StringBinary(BinaryOperatorKind k, KExpr l, KExpr r) => k switch
        {
            BinaryOperatorKind.Equals => StringEqual(l, r),
            BinaryOperatorKind.NotEquals => new KOp("!", StringEqual(l, r)),
            _ => new KOp("scat", l, r),
        };

        /// <summary>string.Equals(a, b), a.Equals(b), ordinally (StringComparison.Ordinal, or none); null for any other call.</summary>
        private (IOperation a, IOperation b)? StringEquals(IInvocationOperation inv)
        {
            var m = inv.TargetMethod;
            if (m.Name != "Equals" || !IsString(m.ContainingType)) return null;
            var strings = m.Parameters.TakeWhile(p => IsString(p.Type)).Count();
            var rest = m.Parameters.Skip(strings).ToList();
            if (rest.Count > 1 || rest.Count == 1 && !(rest[0].Type.Name == "StringComparison" &&
                inv.Arguments.First(a => a.Parameter.Ordinal == rest[0].Ordinal).Value.ConstantValue is { HasValue: true, Value: 4 })) return null;
            if (m.IsStatic && strings == 2) return (inv.Arguments.First(a => a.Parameter.Ordinal == 0).Value, inv.Arguments.First(a => a.Parameter.Ordinal == 1).Value);
            if (!m.IsStatic && strings == 1 && inv.Instance != null) return (inv.Instance, inv.Arguments.First(a => a.Parameter.Ordinal == 0).Value);
            return null;
        }

        /// <summary>The same in every state: of its own parameters, constants, this, and variables never written after they're declared.</summary>
        private bool Steady(IOperation op, ISet<ISymbol> own) => op.DescendantsAndSelf().All(o => o.ConstantValue.HasValue || o switch
        {
            IBinaryOperation or IUnaryOperation or IParenthesizedOperation or IConditionalOperation or IInstanceReferenceOperation => true,
            IConversionOperation conv => !IsFunc(conv.Type),
            // (sets of objects made of what's steady: ObjSet.Of(o), .Add, .Union, ObjSet.Empty)
            IInvocationOperation set when IsObjSet(set.TargetMethod.ContainingType) && set.TargetMethod.Name is "Of" or "Add" or "Union" => true,
            IArgumentOperation _ => true,
            IFieldReferenceOperation { Field.Name: "Empty", Instance: null } empty when IsObjSet(empty.Type) => true,
            IPropertyReferenceOperation { Property.Name: "Empty", Instance: null } emptyp when IsObjSet(emptyp.Type) => true,
            IParameterReferenceOperation p => own.Contains(p.Parameter) || NeverWritten(p.Parameter),
            ILocalReferenceOperation l => NeverWritten(l.Local),
            _ => false,
        });
    }
}
