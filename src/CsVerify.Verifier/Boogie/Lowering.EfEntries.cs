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
    /// EF's entries as values. ctx.Entry(o) is its context and its entity; entry.Property(x => x.P), Property("Name") or
    /// Property&lt;T&gt;("Name") of one is that and a column, a property of the class or a shadow column. They are held
    /// as those parts wherever the program keeps them (locals, the flow graph's captures), and read for State,
    /// CurrentValue and OriginalValue, set for State, and reloaded. Another use of one isn't translated.
    /// </summary>
    internal sealed partial class Lowering
    {
        private sealed class EntryParts
        {
            public KExpr C, O;
            public EfModel.Entity E;
            /// <summary>Of a property entry: its column, a property of the class or a shadow one (its name and type).</summary>
            public IPropertySymbol Property;
            public string Shadow;
            public ITypeSymbol ColumnType;
            public bool IsColumn => Property != null || Shadow != null;
        }

        private readonly Dictionary<ILocalSymbol, EntryParts> _entryLocals = new Dictionary<ILocalSymbol, EntryParts>(SymbolEqualityComparer.Default);
        private readonly Dictionary<CaptureId, EntryParts> _entryCaptures = new Dictionary<CaptureId, EntryParts>();

        /// <summary>EF's EntityEntry or PropertyEntry (generic or not).</summary>
        internal static bool IsEntryType(ITypeSymbol t) =>
            t is INamedTypeSymbol { Name: "EntityEntry" or "PropertyEntry" } n && n.ContainingNamespace?.ToDisplayString() == "Microsoft.EntityFrameworkCore.ChangeTracking";

        /// <summary>The entry an operation is, evaluating what it needs (null where it isn't one the model follows).</summary>
        private EntryParts EntryAt(IOperation op)
        {
            switch (Unconverted(op))
            {
                case IInvocationOperation { TargetMethod.Name: "Entry" } entry when EntryOf(entry) is var (c, o, e):
                    return new EntryParts { C = c, O = o, E = e };
                case IInvocationOperation { TargetMethod.Name: "Property", Instance: { } of } prop when IsEntryType(of.Type):
                    return WithColumn(EntryAt(of), prop);
                case ILocalReferenceOperation l when _entryLocals.TryGetValue(l.Local, out var held):
                    return held;
                case IFlowCaptureReferenceOperation r when _entryCaptures.TryGetValue(r.Id, out var captured):
                    return captured;
                default:
                    return null;
            }
        }

        /// <summary>A Property call of an entry: the entry and the column it names (null where it names none the model has).</summary>
        private EntryParts WithColumn(EntryParts en, IInvocationOperation prop) =>
            en is { IsColumn: false } && ColumnOfEntry(prop) is var (p, shadow, type) && SymbolEqualityComparer.Default.Equals(Column(en.E, p, shadow), type)
                ? new EntryParts { C = en.C, O = en.O, E = en.E, Property = p, Shadow = p == null ? shadow : null, ColumnType = type }
                : null;

        /// <summary>An inlined method's entry locals (InlinedBody), in a specification.</summary>
        private readonly Dictionary<ILocalSymbol, EntryParts> _specEntries = new Dictionary<ILocalSymbol, EntryParts>(SymbolEqualityComparer.Default);

        /// <summary>The entry an operation is, in a specification: its parts as terms.</summary>
        private EntryParts SpecEntryAt(IOperation op, IParameterSymbol result)
        {
            switch (Unconverted(op))
            {
                case IInvocationOperation { TargetMethod.Name: "Entry", Instance: { } ctx, Arguments: [var arg] } when KernelTypes.Ef.IsContextType(ctx.Type) &&
                                                                                                                 KernelTypes.Ef.EntityOf(Unconverted(arg.Value).Type) is EfModel.Entity e:
                    return new EntryParts { C = Spec(ctx, result), O = Spec(Unconverted(arg.Value), result), E = e };
                case IInvocationOperation { TargetMethod.Name: "Property", Instance: { } of } prop when IsEntryType(of.Type):
                    return WithColumn(SpecEntryAt(of, result), prop);
                case ILocalReferenceOperation l when _specEntries.TryGetValue(l.Local, out var bound):
                    return bound;
                case ILocalReferenceOperation l when _entryLocals.TryGetValue(l.Local, out var held):
                    return held;
                default:
                    return null;
            }
        }

        /// <summary>
        /// EntryRead's, in a specification: defined where the context and the entity aren't null (else Entry throws); a
        /// shadow column's or an original value, of the entity, not known (a map fresh at each application).
        /// </summary>
        private KExpr SpecEntryRead(IPropertyReferenceOperation pr, IParameterSymbol result)
        {
            var en = SpecEntryAt(pr.Instance, result) ?? throw new NotTranslated("EF's entry, of what the verifier can't follow");
            var defined = AndAlso(NotNull(en.C), NotNull(en.O));
            switch (pr.Property.Name)
            {
                case "State" when !en.IsColumn:
                    return new KOp("$need", defined, State(en.C, en.O));
                case "CurrentValue" when en.Property != null:
                    _p.AddField(en.Property.OriginalDefinition);
                    return new KOp("$need", defined, Column(en.Property, en.O));
                case "CurrentValue" or "OriginalValue" when en.IsColumn && InSubset(en.ColumnType):
                    return new KOp("$need", defined, Sel(new KVar(ValueMap(en.ColumnType)), en.O));
                default:
                    throw new NotTranslated("EF's " + pr.Property.Name + " of an entry");
            }
        }

        /// <summary>
        /// The column a Property call of an entry names, without evaluating anything: by a lambda of the row's property,
        /// or by its name (the class's property of the name, else the model's shadow column); its type. Null where it
        /// names none the model has.
        /// </summary>
        private (IPropertySymbol p, string shadow, ITypeSymbol type)? ColumnOfEntry(IInvocationOperation prop)
        {
            var entity = (prop.Instance?.Type as INamedTypeSymbol)?.TypeArguments.FirstOrDefault() is ITypeSymbol et ? KernelTypes.Ef.EntityOf(et) : null;
            var arg = prop.Arguments[0].Value;
            if (arg.ConstantValue is { HasValue: true, Value: string name })
            {
                var type = prop.TargetMethod.TypeArguments.FirstOrDefault();
                return entity == null || type == null ? null : (EfModel.PropertiesOf(entity.Type).FirstOrDefault(x => x.Name == name && IsField(x)), name, type);
            }
            return PureLambda(arg) is var (body, p1, _) && Unconverted(body) is IPropertyReferenceOperation { Instance: IParameterReferenceOperation r, Property: var p } &&
                   SymbolEqualityComparer.Default.Equals(r.Parameter, p1) && IsField(p)
                ? (p, null, p.Type)
                : null;
        }

        /// <summary>The type of an entity's column by its property or shadow name; null where it has none.</summary>
        private static ITypeSymbol Column(EfModel.Entity e, IPropertySymbol p, string shadow) =>
            p != null ? p.Type : e.Shadow.TryGetValue(shadow, out var t) ? t : null;

        /// <summary>An entry kept in a local: its parts in variables of their own, the column the same at each assignment.</summary>
        private void EntryAssign(ILocalSymbol l, IOperation value)
        {
            var v = EntryAt(value) ?? throw new NotTranslated("EF's entry, of what the verifier can't follow");
            _entryLocals[l] = Hold(Local(l), v, _entryLocals.TryGetValue(l, out var was) ? was : null);
        }

        private void EntryCapture(IFlowCaptureOperation fc)
        {
            var v = EntryAt(fc.Value) ?? throw new NotTranslated("EF's entry, of what the verifier can't follow");
            _entryCaptures[fc.Id] = Hold("c$" + fc.Id.GetHashCode(), v, _entryCaptures.TryGetValue(fc.Id, out var was) ? was : null);
        }

        private EntryParts Hold(string name, EntryParts v, EntryParts was)
        {
            if (was != null && (!ReferenceEquals(was.E, v.E) || !SymbolEqualityComparer.Default.Equals(was.Property, v.Property) || was.Shadow != v.Shadow))
            {
                throw new NotTranslated("EF's entry, of a different entity or column where it's assigned again");
            }
            var c = name + "$ctx";
            var o = name + "$obj";
            if (was == null)
            {
                _p.AddLocal(KLocal.Of(c, "Ref"));
                _p.AddLocal(KLocal.Of(o, "Ref"));
            }
            Emit(KAssign.Of(c, v.C));
            Emit(KAssign.Of(o, v.O));
            return new EntryParts { C = new KVar(c), O = new KVar(o), E = v.E, Property = v.Property, Shadow = v.Shadow, ColumnType = v.ColumnType };
        }

        /// <summary>
        /// A read of an entry's State, or a property entry's CurrentValue (the entity's property; a shadow column's, a value
        /// of its type) or OriginalValue (a value of its type); null for another property.
        /// </summary>
        private KExpr EntryRead(IPropertyReferenceOperation pr)
        {
            if (pr.Instance == null || !IsEntryType(pr.Instance.Type) || pr.Property.Name is not ("State" or "CurrentValue" or "OriginalValue"))
            {
                return null;
            }
            var en = EntryAt(pr.Instance) ?? throw new NotTranslated("EF's entry, of what the verifier can't follow");
            switch (pr.Property.Name)
            {
                case "State" when !en.IsColumn:
                    return State(en.C, en.O);
                case "CurrentValue" when en.Property != null:
                    _p.AddField(en.Property.OriginalDefinition);
                    return new KField
                    {
                        Field = en.Property.OriginalDefinition,
                        Instance = en.O,
                        OnThis = false,
                        At = pr.Syntax,
                        InstanceAt = pr.Syntax,
                    };
                case "CurrentValue" or "OriginalValue" when en.IsColumn:
                    return Unknown(null, en.ColumnType, notNull: en.Property != null && en.E.NotNullColumn(en.Property) || en.ColumnType.IsValueType);
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
