using System.Collections.Generic;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.FlowAnalysis;
using Microsoft.CodeAnalysis.Operations;
using static CsVerify.Verifier.Boogie.KernelTypes;
using static CsVerify.Verifier.Boogie.KOp;

namespace CsVerify.Verifier.Boogie
{
    /// <summary>
    /// The relational type of a database query: of the rows of one table, through operators that keep or drop rows and
    /// map each to one value, which columns identify a row (its keys), which a filter fixes, and what order the rows
    /// are in. Keys follow the standard derivation of unique keys: a table's are its key and unique indexes, and those
    /// of what a one-to-one navigation leads to; a filter that fixes every column of a key keeps one row at most; a
    /// projection keeps the rows, one to one, in their order. Columns are paths of property names from the table's
    /// row; a projection's members are read back to them.
    /// </summary>
    internal sealed partial class Lowering
    {
        private sealed class RelKey
        {
            public HashSet<string> Columns;
            /// <summary>Every column NOT NULL, of the row itself: no two rows tie in an order by them.</summary>
            public bool Total;
        }

        private sealed class Rel
        {
            public EfModel.Entity Table;
            public List<RelKey> Keys;
            public HashSet<string> Constant = new HashSet<string>();
            /// <summary>The columns the rows are sorted by, outermost first (null: an order the database doesn't fix).</summary>
            public List<string> Order;
            /// <summary>Of a projection: each member's column ("" the row itself); null: the rows are the table's.</summary>
            public Dictionary<string, string> Projection;
            /// <summary>Of a projection whose value is a column or the row ("" ): that; else null.</summary>
            public string ProjectedValue;
            public bool Projected;

            public bool AtMostOne => Keys.Any(k => k.Columns.IsSubsetOf(Constant));
            public bool Ordered => Order != null && Keys.Any(k => k.Total && k.Columns.IsSubsetOf(Order));

            public Rel Copy() => new Rel
            {
                Table = Table,
                Keys = Keys,
                Constant = new HashSet<string>(Constant),
                Order = Order?.ToList(),
                Projection = Projection,
                ProjectedValue = ProjectedValue,
                Projected = Projected,
            };
        }

        /// <summary>The relational type of a database query, or null where it isn't one table's rows through such operators.</summary>
        private Rel RelOf(IOperation op)
        {
            for (int depth = 0; depth < 64 && op != null; depth++)
            {
                op = Unconverted(op);
                switch (op)
                {
                    case IPropertyReferenceOperation pr when DbSetEntity(pr.Type) is EfModel.Entity e:
                        return Scan(e);
                    case IInvocationOperation set when set.TargetMethod.Name == "Set" && DbSetEntity(set.Type) is EfModel.Entity se:
                        return Scan(se);
                    case ILocalReferenceOperation l when Initializer(l) is IOperation init:
                        op = init;
                        continue;
                    case IFlowCaptureReferenceOperation c when _captured.TryGetValue(c.Id, out var cv):
                        op = cv;
                        continue;
                    case IInvocationOperation sh when SourceHelper(sh) is IOperation shv:
                        op = shv;
                        continue;
                    case IInvocationOperation c when (IsQueryableMethod(c.TargetMethod) || IsEfMethod(c.TargetMethod)) && c.Arguments.Length > 0:
                        return Step(c);
                    default:
                        return null;
                }
            }
            return null;
        }

        private static Rel Scan(EfModel.Entity e) => new Rel { Table = e, Keys = KeysOf(e, "", 0, true, filtered: true).ToList() };

        /// <summary>
        /// An entity's keys, as paths from its row: its key and unique indexes, then, of each one-to-one navigation, the
        /// keys of the entity it leads to (a row of either end has one row of the other at most). Those, and a nullable
        /// column's, identify a row only where they aren't null.
        /// </summary>
        private static IEnumerable<RelKey> KeysOf(EfModel.Entity e, string prefix, int depth, bool total, bool filtered)
        {
            // (filtered: of the rows the query filters keep, where a unique index is one only among those)
            foreach (var set in e.Identifying.Concat(filtered ? e.UniqueWhereFiltered : Enumerable.Empty<List<IPropertySymbol>>()).Where(s => s.Count > 0))
            {
                yield return new RelKey { Columns = set.Select(p => prefix + p.Name).ToHashSet(), Total = total && set.All(e.NotNullColumn) };
            }
            if (depth >= 3)
            {
                yield break;
            }
            foreach (var nav in e.References.Where(n => KernelTypes.Ef.OneToOne(n, filtered)))
            {
                if (KernelTypes.Ef.EntityOf(nav.Type) is EfModel.Entity t && !ReferenceEquals(t, e))
                {
                    foreach (var k in KeysOf(t, prefix + nav.Name + ".", depth + 1, false, filtered))
                    {
                        yield return k;
                    }
                }
            }
        }

        private Rel Step(IInvocationOperation c)
        {
            var args = c.Arguments.OrderBy(a => a.Parameter.Ordinal).Where(a => !IsToken(a.Parameter.Type)).ToList();
            var r = RelOf(args[0].Value)?.Copy();
            if (r == null)
            {
                return null;
            }
            switch (c.TargetMethod.Name)
            {
                case "Where" when args.Count == 2:
                    return Filtered(r, args[1].Value);
                case "OrderBy" or "OrderByDescending" or "ThenBy" or "ThenByDescending" when args.Count == 2:
                {
                    var col = PureLambda(args[1].Value) is var (body, p, _) && p != null ? ColumnOf(body, p, r) : null;
                    r.Order = col == null ? null : c.TargetMethod.Name.StartsWith("Then") ? r.Order?.Append(col).ToList() : new List<string> { col };
                    return r;
                }
                case "Select" when args.Count == 2:
                    return Projected(r, args[1].Value);
                case "Distinct" when args.Count == 1:
                    r.Order = null;
                    return r;
                // (every row, the ones the query filters drop too: the keys that hold of them all)
                case "IgnoreQueryFilters":
                    r.Keys = KeysOf(r.Table, "", 0, true, filtered: false).ToList();
                    return r;
                case "Skip" or "Take" or "AsNoTracking" or "AsNoTrackingWithIdentityResolution" or "AsTracking" or "Include" or "ThenInclude" or "AsSplitQuery" or
                    "AsSingleQuery" or "IgnoreAutoIncludes" or "TagWith" or "TagWithCallSite":
                    return r;
                default:
                    return null;
            }
        }

        /// <summary>The rows a predicate keeps: each column it compares, in a conjunct, to a value not of the row is fixed.</summary>
        private Rel Filtered(Rel r, IOperation predicate)
        {
            if (r == null || PureLambda(predicate) is not var (body, p, _) || p == null)
            {
                return r;
            }
            r = r.Copy();
            foreach (var c in Conjuncts(Unconverted(body)))
            {
                if (c is IBinaryOperation { OperatorKind: BinaryOperatorKind.Equals } eq &&
                    (FixedColumn(eq.LeftOperand, eq.RightOperand, p, r) ?? FixedColumn(eq.RightOperand, eq.LeftOperand, p, r)) is string col)
                {
                    r.Constant.Add(col);
                }
            }
            return r;
        }

        /// <summary>A projection: the rows, one to one, in their order; its members read back to the columns they are.</summary>
        private Rel Projected(Rel r, IOperation selector)
        {
            // (its members' columns, of the rows it maps)
            var projection = new Dictionary<string, string>();
            string value = null;
            // (which columns its members are doesn't depend on what else it does: a selector that makes an object too)
            if (LambdaBody(selector) is var (body, p) && p != null)
            {
                var b = Unconverted(body);
                // (an anonymous type's members, an object's set in its initializer, a positional record's by its parameters)
                var inits = b is IAnonymousObjectCreationOperation anon ? anon.Initializers
                          : b is IObjectCreationOperation { Initializer: { } oi } ? oi.Initializers : System.Collections.Immutable.ImmutableArray<IOperation>.Empty;
                if (b is IAnonymousObjectCreationOperation or IObjectCreationOperation)
                {
                    foreach (var init in inits.OfType<ISimpleAssignmentOperation>())
                    {
                        if (init.Target is IPropertyReferenceOperation member && PathOf(init.Value, p, r) is string path)
                        {
                            projection[member.Property.Name] = path;
                        }
                    }
                    if (b is IObjectCreationOperation { Constructor: { } ctor } made && PositionalRecord(ctor))
                    {
                        foreach (var a in made.Arguments)
                        {
                            if (PathOf(a.Value, p, r) is string path)
                            {
                                projection[a.Parameter.Name] = path;
                            }
                        }
                    }
                }
                else
                {
                    value = PathOf(b, p, r);
                }
            }
            r.Projected = true;
            r.Projection = projection;
            r.ProjectedValue = value;
            return r;
        }

        /// <summary>A lambda's one expression and its first parameter, whatever the expression does; else null.</summary>
        private (IOperation body, IParameterSymbol p)? LambdaBody(IOperation arg)
        {
            var fn = Unconverted(arg) is IDelegateCreationOperation dc ? dc.Target as IAnonymousFunctionOperation ?? LambdaOf(dc.Target) ?? LambdaBySymbol(dc.Target)
                   : Unconverted(arg) is IAnonymousFunctionOperation quoted ? quoted
                   : Unconverted(arg) is IFlowAnonymousFunctionOperation fq ? LambdaBySymbol(fq) : null;
            return fn != null && fn.Body.Operations.Length == 1 && fn.Body.Operations[0] is IReturnOperation { ReturnedValue: { } body }
                ? (body, fn.Symbol.Parameters.ElementAtOrDefault(0)) : null;
        }

        /// <summary>
        /// A column's value of a query's element, where the element has it: the row's, or a projection's member that is
        /// the column or a navigation on the way to it. With what must not be null on the way (guards). Else null.
        /// </summary>
        private KExpr ColumnOfElement(Rel r, string path, KExpr elem, ITypeSymbol elemType, List<KExpr> guards, out int navigations)
        {
            // (navigations: how many of an entity's the value is read through, which a context that tracks it may hold otherwise)
            navigations = 0;
            var cur = elem;
            var type = elemType;
            var rest = path;
            if (r.Projected)
            {
                if (r.Projection.Count == 0 && r.ProjectedValue is string whole && (path == whole || whole.Length == 0 || path.StartsWith(whole + ".")))
                {
                    rest = path == whole ? "" : whole.Length == 0 ? path : path.Substring(whole.Length + 1);
                }
                else if (r.Projection.FirstOrDefault(m => path == m.Value || m.Value.Length == 0 || path.StartsWith(m.Value + ".")) is { Key: { } member } via &&
                         elemType.GetMembers(member).OfType<IPropertySymbol>().FirstOrDefault() is IPropertySymbol mp && IsField(mp))
                {
                    _p.AddField(mp.OriginalDefinition);
                    cur = Column(mp, cur);
                    type = mp.Type;
                    rest = path == via.Value ? "" : via.Value.Length == 0 ? path : path.Substring(via.Value.Length + 1);
                    if (rest.Length > 0)
                    {
                        guards.Add(NotNull(cur));
                    }
                }
                else
                {
                    return null;
                }
            }
            if (rest.Length == 0)
            {
                return cur;
            }
            var names = rest.Split('.');
            for (int k = 0; k < names.Length; k++)
            {
                if (type is not INamedTypeSymbol named || EfModel.PropertiesOf(named).FirstOrDefault(x => x.Name == names[k]) is not IPropertySymbol step || !IsField(step))
                {
                    return null;
                }
                _p.AddField(step.OriginalDefinition);
                cur = Column(step, cur);
                type = step.Type;
                if (k < names.Length - 1)
                {
                    guards.Add(NotNull(cur));
                    navigations++;
                }
            }
            return cur;
        }

        /// <summary>
        /// The rows a database query gives differ in each key of one column NOT NULL that its elements have: the table's
        /// rows are distinct by each key, and a key through one-to-one navigations is one of the rows it leads to,
        /// where they aren't null. As the database has them: of a tracked query, where the context tracked none before.
        /// </summary>
        private void DistinctKeys(IOperation source, LSeq s, SyntaxNode at)
        {
            if (KernelTypes.Ef == null || s.Type == null || RelOf(source) is not Rel r)
            {
                return;
            }
            foreach (var key in r.Keys.Where(k => k.Columns.Count == 1))
            {
                var path = key.Columns.First();
                if (ColumnAt(r.Table, path) is not var (owner, col) || !owner.NotNullColumn(col) || !(col.Type.IsValueType || IsString(col.Type)))
                {
                    continue;
                }
                var i = Atom();
                var j = Atom();
                var gi = new List<KExpr>();
                var gj = new List<KExpr>();
                if (ColumnOfElement(r, path, s.Elem.At(i), s.Type, gi, out int navigations) is not KExpr vi || ColumnOfElement(r, path, s.Elem.At(j), s.Type, gj, out _) is not KExpr vj)
                {
                    continue;
                }
                KExpr differ = Ne(vi, vj);
                foreach (var g in gi.Concat(gj).Reverse())
                {
                    differ = Implies(g, differ);
                }
                // (of each two elements the solver has: by the elements, not by the columns' reads, which it may not have yet)
                var fact = Over(KLit.Zero, s.Length, i, Over(KLit.Zero, s.Length, j, OrElse(Eq(i, j), differ), trigger: new[] { s.Elem.At(j) }), trigger: new[] { s.Elem.At(i) });
                // (a key column of an entity the element holds is its row's, tracked or not: EF throws where one changes;
                // read through an entity's navigations, as the database has them)
                if (navigations == 0 && owner.IsKeyProperty(col))
                {
                    ShapeFact(fact, at);
                }
                else
                {
                    LinqFact(fact, at);
                }
            }
        }

        private static IEnumerable<IOperation> Conjuncts(IOperation op) =>
            op is IBinaryOperation { OperatorKind: BinaryOperatorKind.ConditionalAnd } and
                ? Conjuncts(Unconverted(and.LeftOperand)).Concat(Conjuncts(Unconverted(and.RightOperand)))
                : new[] { op };

        /// <summary>
        /// The table's column a member path from the lambda's parameter names ("" the row itself), through the
        /// projection the parameter is a row of; else null.
        /// </summary>
        private static string PathOf(IOperation e, IParameterSymbol p, Rel r)
        {
            var names = new List<string>();
            var at = Unconverted(e);
            while (at is IPropertyReferenceOperation { Property.IsStatic: false } pr)
            {
                names.Insert(0, pr.Property.Name);
                at = Unconverted(pr.Instance);
            }
            if (at is not IParameterReferenceOperation pp || !SymbolEqualityComparer.Default.Equals(pp.Parameter, p))
            {
                return null;
            }
            string root;
            if (!r.Projected)
            {
                root = "";
            }
            else if (r.Projection.Count > 0 && names.Count > 0 && r.Projection.TryGetValue(names[0], out var member))
            {
                root = member;
                names.RemoveAt(0);
            }
            else if (r.ProjectedValue != null && r.Projection.Count == 0)
            {
                root = r.ProjectedValue;
            }
            else
            {
                return null;
            }
            return string.Join(".", new[] { root }.Concat(names).Where(x => x.Length > 0));
        }

        /// <summary>The column a path names: its entity (the table's, or one its navigations lead to) and its property; else null.</summary>
        private static (EfModel.Entity owner, IPropertySymbol column)? ColumnAt(EfModel.Entity table, string path)
        {
            var owner = table;
            var names = path.Split('.');
            for (int k = 0; k < names.Length - 1; k++)
            {
                var nav = owner.References.FirstOrDefault(x => x.Name == names[k]);
                owner = nav == null ? null : KernelTypes.Ef.EntityOf(nav.Type);
                if (owner == null)
                {
                    return null;
                }
            }
            return EfModel.PropertiesOf(owner.Type).FirstOrDefault(x => x.Name == names[^1]) is IPropertySymbol col && IsField(col) ? (owner, col) : null;
        }

        /// <summary>A column a key lambda orders by: one of the row, a scalar, a string or a converted one.</summary>
        private static string ColumnOf(IOperation body, IParameterSymbol p, Rel r) =>
            PathOf(body, p, r) is string path && path.Length > 0 && ColumnAt(r.Table, path) is var (owner, col) && ScalarColumn(owner, col) ? path : null;

        /// <summary>A column compared alike in the database and here: of a value type, a string, or stored by a converter.</summary>
        private static bool ScalarColumn(EfModel.Entity owner, IPropertySymbol col) =>
            col.Type.IsValueType || col.Type.SpecialType == SpecialType.System_String || owner.Converted.Contains(col.OriginalDefinition);

        /// <summary>
        /// The column a value not of the row is compared to, where that fixes it: a scalar column (ScalarColumn), NOT NULL or
        /// compared to a value not null (a null matches each row whose column is null). How .NET compares them doesn't
        /// matter: the database finds the row as it keeps the index unique, by the column's collation or its stored value.
        /// </summary>
        private string FixedColumn(IOperation column, IOperation value, IParameterSymbol p, Rel r)
        {
            if (value.DescendantsAndSelf().OfType<IParameterReferenceOperation>().Any(x => SymbolEqualityComparer.Default.Equals(x.Parameter, p)) ||
                PathOf(column, p, r) is not string path || path.Length == 0 || ColumnAt(r.Table, path) is not var (owner, col) || !ScalarColumn(owner, col))
            {
                return null;
            }
            var v = Unconverted(value);
            bool notNull = v.Type is { IsValueType: true } vt && vt.OriginalDefinition.SpecialType != SpecialType.System_Nullable_T ||
                           v.Type is { IsReferenceType: true } && v.Syntax != null && v.Syntax.SyntaxTree == _model.SyntaxTree &&
                           _model.GetTypeInfo(v.Syntax).Nullability.FlowState == NullableFlowState.NotNull;
            // (through a navigation, a column is null where the navigation is: only a value not null fixes it there)
            return !path.Contains('.') && owner.NotNullColumn(col) || notNull ? path : null;
        }
    }
}
