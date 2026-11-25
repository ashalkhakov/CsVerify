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
    /// EF's entries as values. ctx.Entry(o) is $entry(c, o), a reference its context and its entity are read back from
    /// ($ectx, $eobj); entry.Property(...) of one is $pentry(e, k), of an entry and a column of the model. As
    /// references they are kept in locals, passed to methods and returned like any other. An entry's State is the
    /// tracker's of its context and entity; a property entry's CurrentValue is the entity's property where the column
    /// is known where it's read (through locals and the program's methods read as their bodies), else a value of its
    /// type, as a shadow column's and an OriginalValue are.
    /// </summary>
    internal sealed partial class Lowering
    {
        /// <summary>EF's EntityEntry or PropertyEntry (generic or not).</summary>
        internal static bool IsEntryType(ITypeSymbol t) =>
            t is INamedTypeSymbol { Name: "EntityEntry" or "PropertyEntry" } n && n.ContainingNamespace?.ToDisplayString() == "Microsoft.EntityFrameworkCore.ChangeTracking";

        private static bool IsPropertyEntry(ITypeSymbol t) => t is INamedTypeSymbol { Name: "PropertyEntry" } && IsEntryType(t);

        /// <summary>A column's number, the same in every run: of its entity's and its own name.</summary>
        private static string ColumnId(EfModel.Entity e, string name)
        {
            uint h = 2166136261;
            foreach (char c in e?.Type.ToDisplayString() + "." + name)
            {
                h = (h ^ c) * 16777619;
            }
            return (h & 0x7fffffff).ToString();
        }

        /// <summary>
        /// The entry an operation is, as a term: Entry(o) and Property(...) by what they are of; any other (a local, a
        /// parameter, a call's result) the reference it is, which must not be null where it's used.
        /// </summary>
        private KExpr EntryTerm(IOperation op, IParameterSymbol result, bool spec)
        {
            op = Unconverted(op);
            switch (op)
            {
                case IInvocationOperation { TargetMethod.Name: "Entry", Instance: { } ctx, Arguments: [var arg] } entry when KernelTypes.Ef.IsContextType(ctx.Type):
                {
                    if (KernelTypes.Ef.EntityOf(Unconverted(arg.Value).Type) == null)
                    {
                        throw new NotTranslated("EF's Entry of what isn't an entity");
                    }
                    if (spec)
                    {
                        var c = Spec(ctx, result);
                        var o = Spec(Unconverted(arg.Value), result);
                        return new KOp("$need", AndAlso(NotNull(c), NotNull(o)), new KOp("$entry", c, o));
                    }
                    var (ec, eo, _) = EntryOf(entry) ?? throw new NotTranslated("EF's Entry of what isn't an entity");
                    return new KOp("$entry", ec, eo);
                }
                case IInvocationOperation { TargetMethod.Name: "Property", Instance: { } of, Arguments.Length: 1 } prop when IsEntryType(of.Type):
                {
                    // (of a type parameter's entity: the column its name says, of whichever entity it is called with)
                    if ((of.Type as INamedTypeSymbol)?.TypeArguments.FirstOrDefault() is ITypeParameterSymbol && prop.Arguments[0].Value.ConstantValue is { HasValue: true, Value: string named })
                    {
                        return new KOp("$pentry", EntryTerm(of, result, spec), new KLit(ColumnId(null, named)));
                    }
                    var (e, p, shadow, _) = ColumnOfEntry(prop) ?? throw new NotTranslated("EF's entry, of a column the model hasn't");
                    return new KOp("$pentry", EntryTerm(of, result, spec), new KLit(ColumnId(e, p?.Name ?? shadow)));
                }
                // (a method of the program that gives an entry of its arguments and does nothing else, an extension naming a
                // column say: the entry its body is, of the arguments)
                case IInvocationOperation call when call.TargetMethod.DeclaringSyntaxReferences.Length > 0 && InlinedBody(call) is var (locals, value) && locals.Count == 0 &&
                                                    IsEntryType(value.Type) && Pure(value, null, 0):
                {
                    if (spec)
                    {
                        return SpecInlined(call, result);
                    }
                    var bound = new List<IParameterSymbol>();
                    foreach (var a in call.Arguments.OrderBy(a => a.Parameter.Ordinal))
                    {
                        var x = Once(a.Value);
                        if (x is not KVar { Name: var name })
                        {
                            name = Declare("t$" + _temps++, a.Value.Type);
                            Emit(KAssign.Of(name, x));
                        }
                        var parameter = a.Parameter.OriginalDefinition;
                        if (_assigned.ContainsKey(parameter))
                        {
                            throw new NotTranslated("an entry's method called within itself");
                        }
                        _assigned[parameter] = name;
                        bound.Add(parameter);
                    }
                    try
                    {
                        return EntryTerm(value, null, spec: false);
                    }
                    finally
                    {
                        foreach (var parameter in bound)
                        {
                            _assigned.Remove(parameter);
                        }
                    }
                }
                default:
                {
                    if (spec)
                    {
                        var v = Spec(op, result);
                        return new KOp("$need", NotNull(v), v);
                    }
                    var x = Once(op);
                    Emit(KCheck.Of(NotNull(x), "CSV1013", op.Syntax, $"'{op.Syntax}' might be null: an entry is read of it"));
                    return x;
                }
            }
        }

        /// <summary>
        /// The column a Property call of an entry names, without evaluating anything: by a lambda of the row's property,
        /// or by its name (the class's property of the name, else the model's shadow column), of the type the call
        /// says. Null where the model has no such column.
        /// </summary>
        private (EfModel.Entity e, IPropertySymbol p, string shadow, ITypeSymbol type)? ColumnOfEntry(IInvocationOperation prop, EfModel.Entity of = null)
        {
            // (of: the entity where the entry is read, for a generic method's entry of its type parameter)
            var entity = (prop.Instance?.Type as INamedTypeSymbol)?.TypeArguments.FirstOrDefault() is ITypeSymbol et && KernelTypes.Ef.EntityOf(et) is EfModel.Entity own ? own : of;
            if (entity == null)
            {
                return null;
            }
            var arg = prop.Arguments[0].Value;
            if (arg.ConstantValue is { HasValue: true, Value: string name })
            {
                var p = EfModel.PropertiesOf(entity.Type).FirstOrDefault(x => x.Name == name && IsField(x));
                var type = p?.Type ?? (entity.Shadow.TryGetValue(name, out var st) ? st : null);
                var said = prop.TargetMethod.TypeArguments.FirstOrDefault();
                return type == null || said != null && !SymbolEqualityComparer.Default.Equals(type, said) ? null : (entity, p, p == null ? name : null, type);
            }
            return PureLambda(arg) is var (body, p1, _) && Unconverted(body) is IPropertyReferenceOperation { Instance: IParameterReferenceOperation r, Property: var lp } &&
                   SymbolEqualityComparer.Default.Equals(r.Parameter, p1) && IsField(lp)
                ? (entity, lp, null, lp.Type)
                : null;
        }

        /// <summary>
        /// The column a property entry is of, where that is known where it's read: its Property call, through locals
        /// set once, the flow graph's captures and the program's methods read as their bodies. Else null.
        /// </summary>
        private (EfModel.Entity e, IPropertySymbol p, string shadow, ITypeSymbol type)? StaticColumn(IOperation op, int depth = 0, EfModel.Entity entity = null)
        {
            op = Unconverted(op);
            // (the entity, from where it's read: a generic method's body names only its type parameter)
            entity ??= IsPropertyEntry(op.Type) && ((INamedTypeSymbol)op.Type).TypeArguments.FirstOrDefault() is ITypeSymbol et ? KernelTypes.Ef.EntityOf(et) : null;
            switch (op)
            {
                case IInvocationOperation { TargetMethod.Name: "Property", Instance: { } of, Arguments.Length: 1 } prop when IsEntryType(of.Type):
                    return ColumnOfEntry(prop, entity);
                case ILocalReferenceOperation l when depth < 8 && Initializer(l) is IOperation init:
                    return StaticColumn(init, depth + 1, entity);
                case IFlowCaptureReferenceOperation c when depth < 8 && _captured.TryGetValue(c.Id, out var cv):
                    return StaticColumn(cv, depth + 1, entity);
                case IInvocationOperation call when depth < 8 && call.TargetMethod.DeclaringSyntaxReferences.Length > 0 && InlinedBody(call) is var (_, value):
                    return StaticColumn(value, depth + 1, entity);
                default:
                    return null;
            }
        }

        /// <summary>A reference, evaluated once: itself, or a variable of its value.</summary>
        private KExpr RefOnce(KExpr e)
        {
            if (e is KVar || e is KLit)
            {
                return e;
            }
            var t = "t$" + _temps++;
            _p.AddLocal(KLocal.Of(t, "Ref"));
            Emit(KAssign.Of(t, e));
            return new KVar(t);
        }

        /// <summary>An entry's context, entity and entity type, of an operation of an entry's or a property entry's type.</summary>
        private (KExpr c, KExpr o, EfModel.Entity e) EntryParts(IOperation op, IParameterSymbol result, bool spec)
        {
            var x = EntryTerm(op, result, spec);
            var entry = IsPropertyEntry(Unconverted(op).Type) ? new KOp("$pof", x) : x;
            var entity = (Unconverted(op).Type as INamedTypeSymbol)?.TypeArguments.FirstOrDefault() is ITypeSymbol et ? KernelTypes.Ef.EntityOf(et) : null;
            return (new KOp("$ectx", entry), new KOp("$eobj", entry), entity);
        }

        /// <summary>
        /// A read of an entry's State, or a property entry's CurrentValue (the entity's property, where the column is
        /// known and the class has it; else a value of its type) or OriginalValue (a value of its type); null for
        /// another property.
        /// </summary>
        private KExpr EntryRead(IPropertyReferenceOperation pr, IParameterSymbol result, bool spec)
        {
            if (KernelTypes.Ef == null || pr.Instance == null || !IsEntryType(pr.Instance.Type) || pr.Property.Name is not ("State" or "CurrentValue" or "OriginalValue"))
            {
                return null;
            }
            bool column = IsPropertyEntry(pr.Instance.Type);
            var known = column ? StaticColumn(pr.Instance) : null;
            var (c, o, _) = EntryParts(pr.Instance, result, spec);
            switch (pr.Property.Name)
            {
                case "State" when !column:
                    return State(c, o);
                case "CurrentValue" when known is { p: { } p }:
                    _p.AddField(p.OriginalDefinition);
                    return new KField
                    {
                        Field = p.OriginalDefinition,
                        Instance = o,
                        OnThis = false,
                        NoNull = spec,
                        At = pr.Syntax,
                        InstanceAt = pr.Syntax,
                    };
                case "CurrentValue" or "OriginalValue" when column && InSubset(pr.Type):
                {
                    bool notNull = pr.Type.IsValueType || known is { p: { } np, e: var ne } && ne.NotNullColumn(np);
                    return spec ? Sel(new KVar(ValueMap(pr.Type)), o) : Unknown(null, pr.Type, notNull);
                }
                default:
                    throw new NotTranslated("EF's " + pr.Property.Name + " of an entry");
            }
        }

        /// <summary>
        /// Is the operation an entry's part that only reads: Entry(o) on a context, an entry's Property(...), or the
        /// lambda naming its column (an expression tree EF reads, never runs)?
        /// </summary>
        private static bool EntryReadOnly(IOperation op) => op switch
        {
            IInvocationOperation { TargetMethod.Name: "Entry", Instance: { } c } inv => KernelTypes.Ef != null && KernelTypes.Ef.IsContextType(c.Type) && inv.Arguments.Length == 1,
            IInvocationOperation { TargetMethod.Name: "Property", Instance: { } en } => IsEntryType(en.Type),
            IAnonymousFunctionOperation fn => ColumnLambda(fn),
            _ => false,
        };

        /// <summary>A lambda that names an entry's column, Property(x => x.P): an expression tree EF reads.</summary>
        private static bool ColumnLambda(IAnonymousFunctionOperation fn)
        {
            IOperation op = fn;
            while (op.Parent is IConversionOperation or IDelegateCreationOperation or IParenthesizedOperation)
            {
                op = op.Parent;
            }
            return op.Parent is IArgumentOperation { Parent: IInvocationOperation { TargetMethod.Name: "Property", Instance: { } en } } && IsEntryType(en.Type);
        }
    }
}
