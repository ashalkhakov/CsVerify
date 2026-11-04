using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// <c>Nullable&lt;T&gt;</c> (<c>int?</c>): a value with two functions of it, whether it has a value
    /// (<c>nullable.has</c>) and the value (<c>nullable.value</c>, meaningful only when it has one). <c>some(x)</c> and
    /// <c>none</c> build them. Conversions wrap and unwrap (an explicit unwrap of null throws:
    /// CSV1013), <c>HasValue</c>/<c>Value</c>/<c>GetValueOrDefault</c> read them, <c>x == null</c> and patterns test
    /// them, and lifted operators (<c>x + 1</c>, <c>x &lt; y</c>, <c>x == y</c>) work on the values where both have
    /// one, as C# defines them.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        internal static bool IsNullableValue(ITypeSymbol t) => t?.OriginalDefinition.SpecialType == SpecialType.System_Nullable_T;

        private static ITypeSymbol Underlying(ITypeSymbol nullable) => ((INamedTypeSymbol)nullable).TypeArguments[0];

        private Term HasValue(Term v) => _z3.Apply("nullable.has", Sort.Bool, new[] { T.Coerce(v, Sort.Int) });

        /// <summary>The value of a nullable of type <paramref name="nullable"/>, in its underlying type's range.</summary>
        private Term ValueOf(Term v, ITypeSymbol nullable)
        {
            var u = Underlying(nullable);
            return InRangeOf(_z3.Apply("nullable.value", SortOf(u), new[] { T.Coerce(v, Sort.Int) }), u);
        }

        private Term Some(Term x, ITypeSymbol nullable)
        {
            var u = Underlying(nullable);
            x = T.Coerce(x, SortOf(u));
            var v = _z3.Apply("nullable.some", Sort.Int, new[] { x });
            AssumeSide(T.And(HasValue(v), T.Eq(_z3.Apply("nullable.value", SortOf(u), new[] { v }), x)));
            return v;
        }

        private Term None()
        {
            var v = _z3.Apply("nullable.none", Sort.Int, System.Array.Empty<Term>());
            AssumeSide(T.Not(HasValue(v)));
            return v;
        }

        /// <summary>A nullable whose value is <paramref name="value"/> where <paramref name="has"/> holds, and none elsewhere.</summary>
        private Term SomeWhen(Term has, Term value, ITypeSymbol nullable)
        {
            if (has == T.True) return Some(value, nullable);
            var v = _z3.Fresh("nullable", Sort.Int);
            AssumeSide(T.Eq(HasValue(v), has));
            AssumeSide(T.Implies(has, T.Eq(_z3.Apply("nullable.value", SortOf(Underlying(nullable)), new[] { v }), T.Coerce(value, SortOf(Underlying(nullable))))));
            return v;
        }

        /// <summary>A conversion to or from a nullable value type.</summary>
        private Term NullableConversion(IConversionOperation c, Term v)
        {
            var from = c.Operand.Type;
            bool toNullable = IsNullableValue(c.Type), fromNullable = IsNullableValue(from);
            if (toNullable && !fromNullable)
            {
                if (from == null || IsNullConstant(c.Operand)) return None();
                return Some(UnderlyingConversion(v, from, Underlying(c.Type), c), c.Type);
            }
            if (fromNullable && !toNullable)
            {
                if (c.Type.SpecialType == SpecialType.System_Object || c.Type.TypeKind == TypeKind.Interface)
                {
                    // boxing: null, or a box (its contents are not modeled)
                    var box = Unknown(c.Type, "box");
                    AssumeSide(T.Eq(NotNull(box), HasValue(v)));
                    return box;
                }
                // (T)x throws InvalidOperationException when x has no value
                Require(HasValue(v), "CSV1013", c.Syntax, $"'{c.Operand.Syntax}' might be null where '{c.Syntax}' unwraps it");
                return UnderlyingConversion(ValueOf(v, from), Underlying(from), c.Type, c);
            }
            // int? -> long?: the same presence, the value converted where there is one
            var has = HasValue(v);
            Term inner = null;
            WithGuard(has, () => inner = UnderlyingConversion(ValueOf(v, from), Underlying(from), Underlying(c.Type), c));
            return SomeWhen(has, inner, c.Type);
        }

        /// <summary>A built-in conversion between underlying types (numeric, or none).</summary>
        private Term UnderlyingConversion(Term v, ITypeSymbol from, ITypeSymbol to, IConversionOperation c)
        {
            if (IsFloating(to) && (IsFloating(from) || IsIntegral(from)) || IsFloating(from) && IsIntegral(to))
                return FloatConversion(v, from, to, c);
            if (IsIntegral(to) && IsIntegral(from))
                return Bounded(v, to, c.Syntax, c.IsChecked, $"conversion '{c.Syntax}' to {to.Name} might overflow");
            return T.Coerce(v, SortOf(to));
        }

        /// <summary><c>x.HasValue</c>, <c>x.Value</c>; null for other members.</summary>
        private Term NullableProperty(IPropertyReferenceOperation pr, Frame f, SpecEnv spec)
        {
            switch (pr.Property.Name)
            {
                case "HasValue": return HasValue(Eval(pr.Instance, f, spec));
                case "Value":
                {
                    var v = Eval(pr.Instance, f, spec);
                    Require(HasValue(v), "CSV1013", pr.Syntax, $"'{pr.Syntax}' might be read when '{pr.Instance.Syntax}' is null");
                    return ValueOf(v, pr.Instance.Type);
                }
                default: return null;
            }
        }

        /// <summary><c>x.GetValueOrDefault()</c>, <c>x.GetValueOrDefault(d)</c>; null for other methods.</summary>
        private Term NullableInvocation(IInvocationOperation inv, Frame f, SpecEnv spec)
        {
            if (inv.TargetMethod.Name != "GetValueOrDefault" || inv.Instance == null) return null;
            var v = Eval(inv.Instance, f, spec);
            var u = Underlying(inv.Instance.Type);
            var otherwise = inv.Arguments.Length == 1 ? T.Coerce(Eval(inv.Arguments[0].Value, f, spec), SortOf(u))
                : SortOf(u) == Sort.Bool ? T.False : IsFloating(u) ? Zero(SortOf(u)) : T.Int(0);
            return T.Ite(HasValue(v), ValueOf(v, inv.Instance.Type), otherwise);
        }

        /// <summary>
        /// A lifted operator: on the values where both operands have one. <c>==</c> is also true when neither has;
        /// the comparisons are false when either has none; arithmetic gives none when either has none.
        /// </summary>
        private Term LiftedBinary(IBinaryOperation b, Frame f, SpecEnv spec)
        {
            var l = Eval(b.LeftOperand, f, spec);
            var r = Eval(b.RightOperand, f, spec);
            var lt = b.LeftOperand.Type;
            var rt = b.RightOperand.Type;
            var hl = IsNullConstant(b.LeftOperand) ? T.False : IsNullableValue(lt) ? HasValue(l) : T.True;
            var hr = IsNullConstant(b.RightOperand) ? T.False : IsNullableValue(rt) ? HasValue(r) : T.True;
            var vl = IsNullableValue(lt) ? ValueOf(l, lt) : l;
            var vr = IsNullableValue(rt) ? ValueOf(r, rt) : r;
            var ul = IsNullableValue(lt) ? Underlying(lt) : IsNullConstant(b.LeftOperand) && IsNullableValue(rt) ? Underlying(rt) : lt;
            var both = T.And(hl, hr);
            bool numeric = IsIntegral(ul);
            bool boolean = vl.Sort == Sort.Bool && vr.Sort == Sort.Bool;
            switch (b.OperatorKind)
            {
                case BinaryOperatorKind.Equals when numeric || boolean:
                    return T.Or(T.And(both, T.Eq(vl, vr)), T.And(T.Not(hl), T.Not(hr)));
                case BinaryOperatorKind.NotEquals when numeric || boolean:
                    return T.Not(T.Or(T.And(both, T.Eq(vl, vr)), T.And(T.Not(hl), T.Not(hr))));
                case BinaryOperatorKind.LessThan when numeric: return T.And(both, T.Lt(vl, vr));
                case BinaryOperatorKind.LessThanOrEqual when numeric: return T.And(both, T.Le(vl, vr));
                case BinaryOperatorKind.GreaterThan when numeric: return T.And(both, T.Gt(vl, vr));
                case BinaryOperatorKind.GreaterThanOrEqual when numeric: return T.And(both, T.Ge(vl, vr));
                case BinaryOperatorKind.Add:
                case BinaryOperatorKind.Subtract:
                case BinaryOperatorKind.Multiply:
                case BinaryOperatorKind.Divide:
                case BinaryOperatorKind.Remainder:
                case BinaryOperatorKind.LeftShift:
                case BinaryOperatorKind.RightShift:
                case BinaryOperatorKind.UnsignedRightShift:
                case BinaryOperatorKind.And when numeric:
                case BinaryOperatorKind.Or when numeric:
                case BinaryOperatorKind.ExclusiveOr when numeric:
                    if (!IsNullableValue(b.Type) || !IsIntegral(Underlying(b.Type))) break;
                    Term v = null;
                    WithGuard(both, () => v = Arith(b.OperatorKind, vl, vr, Underlying(b.Type), b.Syntax, false, b.IsChecked));
                    return SomeWhen(both, v, b.Type);
            }
            // (bool? & and |, floating point: three-valued logic and IEEE comparisons are not modeled)
            Warn(b.Syntax, $"lifted operator '{b.Syntax}' is not modeled; its result is unknown");
            return Unknown(b.Type);
        }

        /// <summary>A pattern on a nullable value: null, or a pattern on its value where it has one.</summary>
        private Term NullablePattern(IPatternOperation p, Term v, Frame f, SpecEnv spec)
        {
            var nullable = p.InputType;
            var has = HasValue(v);
            // a part whose input C# has narrowed to the underlying type (the right of "> 0 and < 10") sees the value
            Term Sub(IPatternOperation q) => IsNullableValue(q.InputType) ? Pattern(q, v, f, spec) : Pattern(q, ValueOf(v, nullable), f, spec);
            switch (p)
            {
                case IDiscardPatternOperation _:
                    return T.True;
                case IConstantPatternOperation c when IsNullConstant(c.Value):
                    return T.Not(has);
                case INegatedPatternOperation n:
                    return T.Not(Sub(n.Pattern));
                case IBinaryPatternOperation b:
                {
                    var left = Sub(b.LeftPattern);
                    bool and = b.OperatorKind == BinaryOperatorKind.And;
                    Term right = null;
                    WithGuard(and ? left : T.Not(left), () => right = Sub(b.RightPattern));
                    return and ? T.And(left, right) : T.Or(left, right);
                }
                case IDeclarationPatternOperation d when d.MatchesNull:
                    // var x: the nullable itself
                    if (d.DeclaredSymbol != null) f.Vars[d.DeclaredSymbol] = v;
                    return T.True;
                case IDeclarationPatternOperation d:
                    if (d.DeclaredSymbol != null) f.Vars[d.DeclaredSymbol] = T.Coerce(ValueOf(v, nullable), SortOf(TypeOf(d.DeclaredSymbol)));
                    return has;
                case ITypePatternOperation _:
                    return has;
                default:
                {
                    // 5, > 0, { ... }: on the value, where there is one
                    Term inner = null;
                    WithGuard(has, () => inner = Pattern(p, ValueOf(v, nullable), f, spec, unwrapped: true));
                    return T.And(has, inner);
                }
            }
        }
    }
}
