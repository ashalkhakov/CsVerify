using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.CodeAnalysis.Operations;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Data types and object invariants. A value of a data record (see <see cref="DataTypes"/>) is its constructor
    /// applied to its fields: <c>new Cons(h, t)</c> is the term <c>mk:Cons(h, t)</c>, whose fields read back, whose
    /// tag is Cons's and whose size is one more than its parts'. A type test is a test of the tag, and on the
    /// matching branch the value is that constructor applied to its own fields, so equal fields mean equal values.
    /// Identity is not observable: a data value is its contents.
    /// </summary>
    internal sealed partial class MethodVerifier
    {
        private readonly HashSet<string> _sideFactsDone = new HashSet<string>();
        private readonly HashSet<string> _invariantsInProgress = new HashSet<string>();
        private Term _invariantHeap;
        private int _etaDepth;

        private DataTypes Data => _engine.Data;

        /// <summary>Assumes a fact once per solver scope (at the top level; under a quantifier, every time).</summary>
        private void AssumeOnce(string key, System.Func<Term> fact)
        {
            if (_quantFacts.Count == 0 && !_sideFactsDone.Add(_z3.Scope + ":" + key)) return;
            AssumeSide(fact());
        }

        private Term Tag(Term o) => _z3.Apply("tag", Sort.Int, new[] { o });

        /// <summary>The number of data constructors in a value; null counts 0. The measure of <c>Spec.Decreases(xs)</c>.</summary>
        private Term Size(Term o)
        {
            var size = _z3.Apply("size", Sort.Int, new[] { o });
            AssumeSide(T.Le(T.Int(0), size));
            return T.Ite(T.Eq(o, T.Int(0)), T.Int(0), size);
        }

        private Term ToMeasure(IOperation measure, Term value) => Data.IsData(measure.Type) ? Size(value) : value;

        /// <summary>A positional property of a data value: a selector of its constructor.</summary>
        private Term Field(IPropertySymbol p, Term o, ITypeSymbol staticType)
        {
            var def = p.OriginalDefinition;
            var v = _z3.Apply(def.ToDisplayString(), SortOf(def.Type), new[] { o });
            // what every object of the type satisfies, and that it is one of the type's cases (not from inside a
            // definition being unfolded, where nested definitions are not unfolded and the facts would be empty, nor
            // from inside another case's facts, which would not end)
            if (_unfoldDepth == 0)
            {
                AssumeInvariants(staticType, o);
                if (_etaDepth == 0) Closed(o, staticType);
            }
            // the constructor's non-nullable parameter was proved non-null where the value was built
            if (IsNonNullableType(def.Type)) AssumeSide(T.Implies(NotNull(o), NotNull(v)));
            return v;
        }

        private Term Selector(IPropertySymbol p, Term o) =>
            _z3.Apply(p.OriginalDefinition.ToDisplayString(), SortOf(p.OriginalDefinition.Type), new[] { o });

        /// <summary>The value <c>r(fields)</c>: not null, of r's tag, each field reading back, one bigger than its parts.</summary>
        private Term Construct(INamedTypeSymbol r, IReadOnlyList<Term> values)
        {
            var fields = Data.Fields(r);
            var args = fields.Select((p, i) => T.Coerce(values[i], SortOf(p.OriginalDefinition.Type))).ToArray();
            var o = _z3.Apply("mk:" + r.ToDisplayString(), Sort.Int, args);
            AssumeOnce("mk:" + o.S, () =>
            {
                var facts = new List<Term> { NotNull(o), T.Eq(Tag(o), T.Int(Data.TagOf(r))) };
                var size = T.Int(1);
                for (int i = 0; i < fields.Count; i++)
                {
                    facts.Add(T.Eq(Selector(fields[i], o), args[i]));
                    if (Data.IsData(fields[i].Type)) size = T.Add(size, Size(args[i]));
                }
                facts.Add(T.Eq(_z3.Apply("size", Sort.Int, new[] { o }), size));
                return T.And(facts.ToArray());
            });
            return o;
        }

        /// <summary>
        /// If <paramref name="v"/> is a <paramref name="c"/>, it is c's constructor applied to its own positional
        /// fields, and the fields c gives its base are what its header computes from them (<c>Ind(Prev)</c> has
        /// <c>N == Prev.N + 1</c>). That was checked where the value was built, so here it is a fact.
        /// </summary>
        private void Eta(INamedTypeSymbol c, Term v)
        {
            var primary = DataTypes.PrimaryConstructor(c);
            var args = Enumerable.Range(0, primary?.Parameters.Length ?? 0)
                .Select(i => DataTypes.PositionalProperty(c, i) is IPropertySymbol p ? Selector(p, v) : Unknown(primary.Parameters[i].Type)).ToArray();
            foreach (var p in Data.Fields(c).Where(p => IsNonNullableType(p.OriginalDefinition.Type)))
                AssumeSide(T.Implies(NotNull(v), NotNull(Selector(p, v))));
            List<Term> values;
            _foreignSpec++;
            _etaDepth++;
            bool wasCode = _codeMode;
            _codeMode = false;
            try { values = FieldValues(c, args, new Frame { Heap = InvariantHeap }, null); }
            finally { _foreignSpec--; _etaDepth--; _codeMode = wasCode; }
            var mk = Construct(c, values);
            AssumeOnce("eta:" + c.ToDisplayString() + ":" + v.S, () => T.Implies(T.Eq(Tag(v), T.Int(Data.TagOf(c))), T.Eq(v, mk)));
        }

        /// <summary>A value of a closed type is one of its cases.</summary>
        private void Closed(Term v, ITypeSymbol type)
        {
            if (!(type is INamedTypeSymbol t) || !(Data.Cases(t) is IReadOnlyList<INamedTypeSymbol> cases)) return;
            AssumeOnce("closed:" + t.ToDisplayString() + ":" + v.S, () =>
                T.Implies(NotNull(v), T.Or(cases.Select(c => T.Eq(Tag(v), T.Int(Data.TagOf(c)))).ToArray())));
            foreach (var c in cases) Eta(c, v);
        }

        /// <summary><c>v is matched</c>, for a <paramref name="v"/> of static type <paramref name="input"/>.</summary>
        private Term TypeTest(Term v, ITypeSymbol input, ITypeSymbol matched)
        {
            if (matched == null || DataTypes.Derives(input, matched) || input.AllInterfaces.Contains(matched))
                return MayBeNullType(input) ? NotNull(v) : T.True;
            if (matched is INamedTypeSymbol m && Data.Cases(m) is IReadOnlyList<INamedTypeSymbol> cases && Data.IsData(input))
            {
                Closed(v, input);
                foreach (var c in cases) Eta(c, v);
                return T.And(NotNull(v), T.Or(cases.Select(c => T.Eq(Tag(v), T.Int(Data.TagOf(c)))).ToArray()));
            }
            return _z3.Fresh("is", Sort.Bool);
        }

        /// <summary>Does <paramref name="v"/> match the pattern? Its variables are bound in <paramref name="f"/>.</summary>
        private Term Pattern(IPatternOperation p, Term v, Frame f, SpecEnv spec)
        {
            switch (p)
            {
                case IDiscardPatternOperation _:
                    return T.True;
                case IConstantPatternOperation c when IsNullConstant(c.Value):
                    return MayBeNullType(p.InputType) ? T.Eq(v, T.Int(0)) : T.False;
                case IConstantPatternOperation c when IsIntegral(c.Value.Type) || c.Value.Type?.SpecialType == SpecialType.System_Boolean:
                    return T.Eq(v, T.Coerce(Eval(c.Value, f, spec), v.Sort));
                case IRelationalPatternOperation r when IsIntegral(r.Value.Type) && v.Sort == Sort.Int:
                {
                    var k = Eval(r.Value, f, spec);
                    switch (r.OperatorKind)
                    {
                        case BinaryOperatorKind.LessThan: return T.Lt(v, k);
                        case BinaryOperatorKind.LessThanOrEqual: return T.Le(v, k);
                        case BinaryOperatorKind.GreaterThan: return T.Gt(v, k);
                        case BinaryOperatorKind.GreaterThanOrEqual: return T.Ge(v, k);
                    }
                    break;
                }
                case INegatedPatternOperation n:
                    return T.Not(Pattern(n.Pattern, v, f, spec));
                case IBinaryPatternOperation b:
                {
                    var left = Pattern(b.LeftPattern, v, f, spec);
                    bool and = b.OperatorKind == BinaryOperatorKind.And;
                    Term right = null;
                    WithGuard(and ? left : T.Not(left), () => right = Pattern(b.RightPattern, v, f, spec));
                    return and ? T.And(left, right) : T.Or(left, right);
                }
                case IDeclarationPatternOperation d:
                {
                    var test = d.MatchesNull ? T.True : TypeTest(v, p.InputType, d.MatchedType);
                    if (d.DeclaredSymbol != null) f.Vars[d.DeclaredSymbol] = T.Coerce(v, SortOf(TypeOf(d.DeclaredSymbol)));
                    return test;
                }
                case ITypePatternOperation tp:
                    return TypeTest(v, p.InputType, tp.MatchedType);
                case IRecursivePatternOperation r:
                {
                    var test = TypeTest(v, p.InputType, r.MatchedType);
                    if (r.DeclaredSymbol != null) f.Vars[r.DeclaredSymbol] = v;
                    var matched = r.MatchedType as INamedTypeSymbol;
                    var parts = new List<Term> { test };
                    for (int i = 0; i < r.DeconstructionSubpatterns.Length; i++)
                    {
                        var prop = matched != null && Data.IsData(matched) ? DataTypes.PositionalProperty(matched, i) : null;
                        if (prop == null) { Unsupported(r); return _z3.Fresh("match", Sort.Bool); }
                        var item = T.Coerce(Field(prop, v, matched), SortOf(prop.Type));
                        var sub = r.DeconstructionSubpatterns[i];
                        WithGuard(T.And(parts.ToArray()), () => parts.Add(Pattern(sub, item, f, spec)));
                    }
                    foreach (var ps in r.PropertySubpatterns)
                    {
                        if (!(ps.Member is IPropertyReferenceOperation pr && DataTypes.IsPositional(pr.Property) && Data.IsData(pr.Property.ContainingType)))
                        { Unsupported(ps); return _z3.Fresh("match", Sort.Bool); }
                        var item = T.Coerce(Field(pr.Property, v, matched ?? p.InputType), SortOf(pr.Property.Type));
                        WithGuard(T.And(parts.ToArray()), () => parts.Add(Pattern(ps.Pattern, item, f, spec)));
                    }
                    return T.And(parts.ToArray());
                }
            }
            Unsupported(p);
            return _z3.Fresh("match", Sort.Bool);
        }

        /// <summary>
        /// A switch expression in a specification or a [Pure] definition (code sees it lowered to tests): the first
        /// arm that matches. Falling off the end throws, so a specification must cover every case.
        /// </summary>
        private Term SwitchExpression(ISwitchExpressionOperation sw, Frame f, SpecEnv spec)
        {
            var v = Eval(sw.Value, f, spec);
            var arms = new List<(Term when, Term value)>();
            Term unmatched = T.True;
            foreach (var arm in sw.Arms)
            {
                Term cond = null, value = null;
                WithGuard(unmatched, () =>
                {
                    cond = Pattern(arm.Pattern, v, f, spec);
                    if (arm.Guard != null)
                    {
                        var c0 = cond;
                        WithGuard(c0, () => cond = T.And(c0, AsBool(Eval(arm.Guard, f, spec))));
                    }
                    var c1 = cond;
                    WithGuard(c1, () => value = T.Coerce(Eval(arm.Value, f, spec), SortOf(sw.Type)));
                });
                arms.Add((cond, value));
                unmatched = T.And(unmatched, T.Not(cond));
            }
            Require(T.Not(unmatched), "CSV1012", sw.Syntax, $"switch expression '{sw.Value.Syntax} switch' might not cover every value");
            Term result = Unknown(sw.Type, "nomatch");
            for (int i = arms.Count - 1; i >= 0; i--) result = T.Ite(arms[i].when, arms[i].value, result);
            return result;
        }

        /// <summary><c>new R(...)</c>: a data value, or an object whose constructor's contract is checked and assumed.</summary>
        private Term NewObject(IObjectCreationOperation oc, Frame f, SpecEnv spec)
        {
            var ctor = oc.Constructor;
            var args = new Term[ctor?.Parameters.Length ?? 0];
            foreach (var a in oc.Arguments)
            {
                var v = Eval(a.Value, f, spec);
                NonNullArgument(a, v, ctor);
                if (a.Parameter != null) args[a.Parameter.Ordinal] = v;
            }
            if (oc.Initializer != null) NotModeled(oc.Initializer.Syntax, "object initializers are not supported");
            var type = oc.Type as INamedTypeSymbol;
            if (ctor != null && Data.IsData(type))
            {
                if (!SymbolEqualityComparer.Default.Equals(DataTypes.PrimaryConstructor(type), ctor))
                {
                    NotModeled(oc.Syntax, $"a data record is built with its primary constructor only");
                    return Unknown(oc.Type, "new");
                }
                var o = Construct(type, FieldValues(type, args, f, spec));
                ProveInvariants(type, o, oc.Syntax);
                return o;
            }

            var callee = ctor != null ? _engine.ContractOf(ctor) : null;
            Frame pre = null;
            if (callee?.HasSource == true && _codeMode)
            {
                pre = CalleeFrame(callee, null, args, f.Heap);
                var preEnv = new SpecEnv { Old = pre };
                foreach (var req in callee.Requires)
                    Prove(AsBool(EvalForeignSpec(req, pre, preEnv)), "CSV1001", oc.Syntax,
                        $"precondition '{req.Syntax}' of 'new {type?.Name}' might not hold");
            }
            if (ctor == null || _engine.MayWriteHeap(ctor)) f.Heap = _z3.Fresh("heap", Sort.Heap);
            var obj = Unknown(oc.Type, "new");
            if (MayBeNullType(oc.Type)) _z3.Assume(NotNull(obj));
            if (pre != null)
            {
                var post = pre.Clone();
                post.This = obj;
                post.Heap = f.Heap;
                foreach (var ens in callee.Ensures)
                    _z3.Assume(AsBool(EvalForeignSpec(ens.Expr, post, new SpecEnv { Old = pre, Result = obj, ResultParameter = ens.ResultParameter })));
            }
            return obj;
        }

        /// <summary>
        /// The fields of <c>new t(args)</c>: its own positional parameters, and its base's, which the record header's
        /// base arguments compute from them (<c>record Ind(Fact Prev) : Fact(Prev.N + 1, ...)</c>).
        /// </summary>
        private List<Term> FieldValues(INamedTypeSymbol t, Term[] args, Frame f, SpecEnv spec)
        {
            var values = new Dictionary<IPropertySymbol, Term>(SymbolEqualityComparer.Default);
            CollectFields(t, args, values, f, spec);
            return Data.Fields(t).Select(p => values.TryGetValue(p, out var v) ? v : Unknown(p.Type, p.Name)).ToList();
        }

        private void CollectFields(INamedTypeSymbol t, Term[] args, Dictionary<IPropertySymbol, Term> values, Frame f, SpecEnv spec)
        {
            var primary = DataTypes.PrimaryConstructor(t);
            if (primary == null) return;
            for (int i = 0; i < primary.Parameters.Length; i++)
                if (t.GetMembers(primary.Parameters[i].Name).OfType<IPropertySymbol>().FirstOrDefault(DataTypes.IsPositional) is IPropertySymbol own)
                    values[own] = args[i];
            if (!Data.IsData(t.BaseType)) return;
            var baseArgs = new Term[DataTypes.PrimaryConstructor(t.BaseType)?.Parameters.Length ?? 0];
            var baseSyntax = t.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).OfType<RecordDeclarationSyntax>()
                .SelectMany(d => d.BaseList?.Types.OfType<PrimaryConstructorBaseTypeSyntax>() ?? Enumerable.Empty<PrimaryConstructorBaseTypeSyntax>())
                .FirstOrDefault();
            if (baseSyntax != null)
            {
                var model = _engine.ModelOf(baseSyntax.SyntaxTree);
                var frame = new Frame { Heap = f.Heap };
                for (int i = 0; i < primary.Parameters.Length; i++) frame.Vars[primary.Parameters[i]] = args[i];
                foreach (var arg in baseSyntax.ArgumentList.Arguments)
                    if (model.GetOperation(arg) is IArgumentOperation a && a.Parameter != null)
                        baseArgs[a.Parameter.Ordinal] = Eval(a.Value, frame, spec);
            }
            CollectFields(t.BaseType, baseArgs, values, f, spec);
        }

        /// <summary>Synthesized record <c>==</c> on a type with value equality: equality of the values.</summary>
        private Term RecordEquality(IBinaryOperation b, Frame f, SpecEnv spec)
        {
            var l = Eval(b.LeftOperand, f, spec);
            var r = Eval(b.RightOperand, f, spec);
            Closed(l, b.LeftOperand.Type);
            Closed(r, b.RightOperand.Type);
            var eq = T.Eq(l, r);
            return b.OperatorKind == BinaryOperatorKind.NotEquals ? T.Not(eq) : eq;
        }

        private bool IsRecordEquality(IBinaryOperation b) =>
            b.OperatorMethod != null && b.OperatorMethod.IsImplicitlyDeclared && b.OperatorMethod.ContainingType is INamedTypeSymbol t &&
            Data.IsData(t) && (b.OperatorKind == BinaryOperatorKind.Equals || b.OperatorKind == BinaryOperatorKind.NotEquals) &&
            Data.HasValueEquality(t);

        // ---------------------------------------------------------------------------------- invariants

        private Term InvariantHeap => _invariantHeap ??= _z3.Fresh("noheap", Sort.Heap);

        private Term InvariantHolds(IMethodSymbol inv, Term o) =>
            AsBool(PureApply(_engine.ContractOf(inv), o, System.Array.Empty<Term>(), InvariantHeap, Sort.Bool));

        /// <summary>
        /// Every object of the type satisfies its invariants: proved when it was built, and its fields never change.
        /// (Not while verifying what an invariant depends on, which would make it its own proof.)
        /// </summary>
        private void AssumeInvariants(ITypeSymbol type, Term o)
        {
            if (_engine.IsUnderInvariant(_method)) return;
            var invariants = DataTypes.Invariants(type).ToList();
            if (invariants.Count == 0 || !_invariantsInProgress.Add(o.S)) return;
            try
            {
                foreach (var inv in invariants)
                    AssumeOnce("inv:" + inv.ToDisplayString() + ":" + o.S, () => T.Implies(NotNull(o), InvariantHolds(inv, o)));
            }
            finally { _invariantsInProgress.Remove(o.S); }
        }

        /// <summary>A new object must satisfy its type's invariants (assumed of it nowhere while this is proved).</summary>
        private void ProveInvariants(INamedTypeSymbol type, Term o, SyntaxNode at)
        {
            var invariants = DataTypes.Invariants(type).ToList();
            if (invariants.Count == 0 || !_invariantsInProgress.Add(o.S)) return;
            try
            {
                foreach (var inv in invariants)
                    Require(InvariantHolds(inv, o), "CSV1015", at, $"invariant '{inv.Name}' of {type.Name} might not hold for '{at}'");
            }
            finally { _invariantsInProgress.Remove(o.S); }
        }
    }
}
