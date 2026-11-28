using System.Collections.Generic;
using System.Linq;
using CsVerify.Analyzers;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.Operations;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace CsVerify.Verifier
{
    /// <summary>
    /// Mutable object state. An instance field (or auto-property) of a class declared in the sources is a "heap
    /// field": a map from object to value, which assignments update. A call may change only the heap fields its
    /// callee (or anything it reaches) writes, an inferred frame condition per field, as for arrays.
    /// </summary>
    internal sealed class FieldEffects
    {
        /// <summary>What one method does to heap fields, directly (callees are listed, not included).</summary>
        private sealed class Direct
        {
            public readonly HashSet<ISymbol> Reads = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            public readonly HashSet<ISymbol> Writes = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            /// <summary>A constructor's writes to fields of the object it builds (<c>this.F = ...</c>).</summary>
            public readonly HashSet<ISymbol> SelfWrites = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            public readonly HashSet<IMethodSymbol> Callees = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
            /// <summary>A constructor's: the one it runs on the same object first (this(...), or base(...), written or not).</summary>
            public IMethodSymbol Chained;
            /// <summary>May write any heap field (a virtual call, a library call handed a callback or an object).</summary>
            public bool All;

            public bool AddCallee(IMethodSymbol callee) => Callees.Add(callee);

            public bool AddRead(ISymbol read) => Reads.Add(read);

            public bool AddSelfWrite(ISymbol selfWrite) => SelfWrites.Add(selfWrite);

            public bool AddWrite(ISymbol write) => Writes.Add(write);

            public void AddWrites(IEnumerable<ISymbol> other) => Writes.UnionWith(other);
        }

        private readonly Engine _engine;
        private readonly Dictionary<IMethodSymbol, Direct> _direct = new Dictionary<IMethodSymbol, Direct>(SymbolEqualityComparer.Default);

        public FieldEffects(Engine engine)
        {
            _engine = engine;
        }

        /// <summary>
        /// A member stored as mutable object state: an instance field or auto-property of a source class, or a mutable
        /// static field of one (the field of a single object, <see cref="IsStaticField"/>).
        /// </summary>
        public static bool IsHeapField(ISymbol s)
        {
            if (s == null || !(s.ContainingType is INamedTypeSymbol t) || t.TypeKind != TypeKind.Class)
            {
                return false;
            }
            // (an auto-property of an entity class of a referenced assembly)
            if (s is IPropertySymbol mp && MetadataEntities.Current?.Fields.Contains(mp.OriginalDefinition) == true)
            {
                return true;
            }
            if (t.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace || s.DeclaringSyntaxReferences.Length == 0)
            {
                return false;
            }
            if (s.IsStatic)
            {
                // (a static auto-property is the static field the compiler keeps it in: mutable where it has a setter)
                return s is IFieldSymbol sf ? !sf.IsConst && !sf.IsReadOnly && !sf.IsImplicitlyDeclared : s is IPropertySymbol { SetMethod: not null } sp && IsAutoProperty(sp);
            }
            switch (s)
            {
                case IFieldSymbol f:
                    return !f.IsConst && !f.IsImplicitlyDeclared;
                case IPropertySymbol p:
                    if (p.IsIndexer || p.IsAbstract || p.IsVirtual && !EntityVirtual(p) || p.IsOverride)
                    {
                        return false;
                    }
                    return IsAutoProperty(p);
                default:
                    return false;
            }
        }

        /// <summary>An auto-property: accessors without bodies, declared as a property (positional ones are values).</summary>
        public static bool IsAutoProperty(IPropertySymbol p) =>
            !p.IsIndexer && p.DeclaringSyntaxReferences.Length > 0 &&
            p.DeclaringSyntaxReferences.All(r => r.GetSyntax() is PropertyDeclarationSyntax pd && pd.AccessorList != null &&
                                                 pd.AccessorList.Accessors.All(a => a.Body == null && a.ExpressionBody == null));

        /// <summary>
        /// A static member set once, where its class is initialized, and read ever after: a static readonly field, or a
        /// static auto-property without a setter (the readonly field the compiler keeps it in).
        /// </summary>
        public static bool IsStaticFixed(ISymbol s) =>
            s is IFieldSymbol { IsStatic: true, IsReadOnly: true } || s is IPropertySymbol { IsStatic: true, SetMethod: null } p && IsAutoProperty(p);

        /// <summary>
        /// A virtual property of an entity class nothing overrides: a source class, and EF's proxies, where the program
        /// references them (UseLazyLoadingProxies' would load it where it's read). As a property not virtual (#129).
        /// </summary>
        private static bool EntityVirtual(IPropertySymbol p)
        {
            var c = Boogie.KernelTypes.Compilation;
            if (Boogie.KernelTypes.Ef?.EntityOf(p.ContainingType) == null || c == null ||
                c.ReferencedAssemblyNames.Any(a => a.Name == "Microsoft.EntityFrameworkCore.Proxies"))
            {
                return false;
            }
            if (_entityVirtualOf != c)
            {
                _entityVirtualOf = c;
                _entityVirtual = new Dictionary<ISymbol, bool>(SymbolEqualityComparer.Default);
            }
            if (!_entityVirtual.TryGetValue(p.OriginalDefinition, out var known))
            {
                _entityVirtual[p.OriginalDefinition] = known = NotOverridden(c, p);
            }
            return known;
        }

        [System.ThreadStatic] private static Compilation _entityVirtualOf;
        [System.ThreadStatic] private static Dictionary<ISymbol, bool> _entityVirtual;

        private static bool NotOverridden(Compilation c, IPropertySymbol p)
        {
            return !c.SyntaxTrees.SelectMany(t => t.GetRoot().DescendantNodes().OfType<PropertyDeclarationSyntax>())
                .Any(d => d.Identifier.Text == p.Name && d.Modifiers.Any(m => m.Text == "override") &&
                          c.GetSemanticModel(d.SyntaxTree).GetDeclaredSymbol(d) is IPropertySymbol o && SymbolEqualityComparer.Default.Equals(o.OverriddenProperty?.OriginalDefinition, p.OriginalDefinition));
        }

        /// <summary>
        /// A mutable static field: a heap field of the statics object, the null reference (no object is null, so it
        /// aliases none). It needs no permission; a call changes it if the callee (or anything it reaches) writes it.
        /// </summary>
        public static bool IsStaticField(ISymbol s) => s.IsStatic && IsHeapField(s);

        public static ISymbol Key(ISymbol s) => s.OriginalDefinition;

        private List<ISymbol> _allFields;

        /// <summary>Every heap field in the sources, and the [Model] functions (ghost fields of external objects).</summary>
        public IReadOnlyList<ISymbol> AllFields() => _allFields ??= _engine.SourceTypes
            .SelectMany(t => t.GetMembers()).Where(IsHeapField).Select(Key).Concat(_engine.Models)
            .Concat(MetadataEntities.Current?.Fields ?? Enumerable.Empty<ISymbol>()).Distinct(SymbolEqualityComparer.Default).ToList();

        /// <summary>
        /// The [Model] functions a call of a library member may change: all of them (within its Spec.Modifies, if its
        /// stub has one), except those over strings, which never change. A stub without Spec.Modifies changes none,
        /// except a constructor, which sets up the new object's.
        /// </summary>
        private IEnumerable<ISymbol> MutableModels() =>
            _engine.Models.Where(m => m.Parameters[0].Type.SpecialType != SpecialType.System_String);

        /// <summary>The model functions of a stub's own type (a list's, for List's stub; none for Array's).</summary>
        private IEnumerable<ISymbol> ModelsOf(INamedTypeSymbol type) =>
            MutableModels().Cast<IMethodSymbol>().Where(x => x.Parameters[0].Type is INamedTypeSymbol o &&
                (DataTypes.Derives(o.OriginalDefinition, type.OriginalDefinition) || DataTypes.Derives(type.OriginalDefinition, o.OriginalDefinition)));

        /// <summary>
        /// May a library method without a stub change model state: is it handed (as its receiver, an argument or a
        /// type argument) something that may be, or lead to, an object with [Model] functions?
        /// </summary>
        private bool MayTouchModels(IMethodSymbol m) =>
            _engine.Models.Count > 0 &&
            (m.Parameters.Any(p => ReachesModels(p.Type)) || !m.IsStatic && m.MethodKind != MethodKind.Constructor && ReachesModels(m.ContainingType) ||
             m.ContainingType.TypeArguments.Concat(m.TypeArguments).Any(ReachesModels));

        /// <summary>Could a value of this type be, or hold where a library can reach it, an object with [Model] functions?</summary>
        private bool ReachesModels(ITypeSymbol t)
        {
            if (_engine.Models.Count == 0)
            {
                return false;
            }
            switch (t)
            {
                case null: return false;
                case IArrayTypeSymbol a: return ReachesModels(a.ElementType);
                case ITypeParameterSymbol _: return true;
            }
            if (t.SpecialType == SpecialType.System_String || t.SpecialType == SpecialType.System_Object || t.TypeKind == TypeKind.Interface || t.TypeKind == TypeKind.Delegate)
            {
                return t.SpecialType != SpecialType.System_String;
            }
            // (a model of any object, Tracker.Unshared(object): of no type in particular, #129)
            var modeled = _engine.Models.Select(x => (x.Parameters[0].Type as INamedTypeSymbol)?.OriginalDefinition).Where(x => x != null && x.SpecialType != SpecialType.System_Object);
            if (modeled.Any(x => DataTypes.Derives(t, x) || DataTypes.Derives(x, t)))
            {
                return true;
            }
            return t is INamedTypeSymbol n && n.TypeArguments.Any(ReachesModels);
        }

        private List<INamedTypeSymbol> _ownable;

        /// <summary>
        /// Can an object of this type sit inside an ownership tree (some [Owns] field holds it)? If not, every such
        /// object is the root of its own tree, and a call changes only the ones whose views it gets.
        /// </summary>
        public bool CanBeOwned(ITypeSymbol type)
        {
            _ownable ??= _engine.SourceTypes.SelectMany(t => t.GetMembers().OfType<IFieldSymbol>())
                .Where(SpecSymbols.IsOwnsField).Select(f => (f.Type as INamedTypeSymbol)?.OriginalDefinition).Where(t => t != null).ToList();
            return _ownable.Any(o => DataTypes.Derives(type, o) || DataTypes.Derives(o, type));
        }

        private List<ISymbol> _owned;

        /// <summary>Every heap field of an [Owned] class in the sources.</summary>
        public IReadOnlyList<ISymbol> OwnedFields() => _owned ??= _engine.SourceTypes
            .Where(SpecSymbols.IsOwned).SelectMany(t => t.GetMembers()).Where(m => !m.IsStatic && IsHeapField(m)).Select(Key)
            .Distinct(SymbolEqualityComparer.Default).ToList();

        /// <summary>The heap fields of a class and its source base classes.</summary>
        public static IEnumerable<ISymbol> FieldsOf(ITypeSymbol type)
        {
            for (var t = (type as INamedTypeSymbol)?.OriginalDefinition; t != null; t = t.BaseType?.OriginalDefinition)
            {
                foreach (var m in t.GetMembers())
                {
                    if (!m.IsStatic && IsHeapField(m))
                    {
                        yield return Key(m);
                    }
                }
            }
        }

        /// <summary>
        /// A method as effects are keyed: a source method by its definition, a library method as called (what a
        /// generic one may do depends on its type arguments).
        /// </summary>
        private IMethodSymbol Normal(IMethodSymbol m)
        {
            m = m.ReducedFrom ?? m;
            return m.DeclaringSyntaxReferences.Length > 0 || m.OriginalDefinition.DeclaringSyntaxReferences.Length > 0 ? m.OriginalDefinition : m;
        }

        private Direct DirectOf(IMethodSymbol m)
        {
            m = Normal(m);
            if (_direct.TryGetValue(m, out var d))
            {
                return d;
            }
            _direct[m] = d = new Direct();
            // which body a virtual or interface call runs is not known statically: anything may be written
            if ((m.IsVirtual || m.IsAbstract || m.IsOverride || m.ContainingType?.TypeKind == TypeKind.Interface) &&
                !m.IsSealed && m.ContainingType?.IsSealed != true && !m.IsStatic)
            {
                d.All = true;
            }
            // a data value's constructor builds a value: it changes no state (its header's computed base arguments are pure)
            // (but one that chains to another computes what it hands on: its arguments are read as any code is)
            if (m.MethodKind == MethodKind.Constructor && _engine.Data.IsData(m.ContainingType) && !DataTypes.Delegates(m))
            {
                return d;
            }
            // a constructor nobody wrote a body for (an implicit one, a primary one): its class's initializers, then its
            // base's constructor
            if (IsInstanceConstructor(m) && m.ContainingType.DeclaringSyntaxReferences.Length > 0 &&
                (m.IsImplicitlyDeclared || m.DeclaringSyntaxReferences.Any(r => r.GetSyntax() is TypeDeclarationSyntax)))
            {
                Walk(d, m, Construction(d, m, null));
                return d;
            }
            // a virtual member may run any override: they are all reachable from it
            if (Engine.IsOverridable(m))
            {
                foreach (var o in Overrides(m))
                {
                    d.AddCallee(o);
                }
            }
            var c = _engine.ContractOf(m.OriginalDefinition);
            if (!c.HasSource || c.IsStub)
            {
                // a library method cannot name user fields; it can reach them only by running user code it is handed
                // (its receiver included: a delegate's Invoke)
                d.All = RunsUserCode(m) && !c.IsPure; // (a [Pure] stub says it has no effects: trusted, like all it says)
                LibraryModels(d, m, c);
                return d;
            }
            var bodies = new List<SyntaxNode> { c.Declaration };
            if (IsInstanceConstructor(m))
            {
                bodies.AddRange(Construction(d, m, c.Declaration as ConstructorDeclarationSyntax));
            }
            Walk(d, m, bodies);
            return d;
        }

        private static bool IsInstanceConstructor(IMethodSymbol m) => m.MethodKind == MethodKind.Constructor && !m.IsStatic;

        /// <summary>The instance members of a class that have an initializer, each with it.</summary>
        internal static IEnumerable<(ISymbol member, EqualsValueClauseSyntax init)> Initializers(INamedTypeSymbol type)
        {
            foreach (var member in type.GetMembers().Where(x => !x.IsStatic && (x is IFieldSymbol || x is IPropertySymbol)))
            {
                foreach (var syntax in member.DeclaringSyntaxReferences.Select(r => r.GetSyntax()))
                {
                    if (((syntax as VariableDeclaratorSyntax)?.Initializer ?? (syntax as PropertyDeclarationSyntax)?.Initializer) is EqualsValueClauseSyntax init)
                    {
                        yield return (member, init);
                    }
                }
            }
        }

        /// <summary>The constructor an implicit base() runs: the base class's that takes no argument (none: object's, or none found).</summary>
        internal static IMethodSymbol ImplicitBase(INamedTypeSymbol type)
        {
            var b = type.BaseType;
            if (type.TypeKind != TypeKind.Class || b == null || b.SpecialType == SpecialType.System_Object)
            {
                return null;
            }
            return b.InstanceConstructors.FirstOrDefault(x => x.Parameters.Length == 0) ??
                   b.InstanceConstructors.FirstOrDefault(x => x.Parameters.All(p => p.IsOptional || p.IsParams));
        }

        /// <summary>
        /// What a constructor runs before its body, as C# has it: its class's initializers (which set the new object's
        /// members), then its base's constructor on the same object (base(...), written or not); one that chains to
        /// this(...) runs that one instead. Gives the code of it there is to read: the initializers' values, and a
        /// primary constructor's base arguments.
        /// </summary>
        private List<SyntaxNode> Construction(Direct d, IMethodSymbol ctor, ConstructorDeclarationSyntax declared)
        {
            var code = new List<SyntaxNode>();
            var type = ctor.ContainingType.OriginalDefinition;
            IMethodSymbol chained = null;
            bool toThis = false;
            if (declared?.Initializer is ConstructorInitializerSyntax ci)
            {
                chained = _engine.ModelOf(ci.SyntaxTree).GetSymbolInfo(ci).Symbol as IMethodSymbol;
                toThis = ci.ThisOrBaseKeyword.IsKind(SyntaxKind.ThisKeyword);
            }
            else
            {
                foreach (var based in ctor.DeclaringSyntaxReferences.Select(r => r.GetSyntax()).OfType<TypeDeclarationSyntax>()
                             .SelectMany(td => td.BaseList?.Types.OfType<PrimaryConstructorBaseTypeSyntax>() ?? Enumerable.Empty<PrimaryConstructorBaseTypeSyntax>()))
                {
                    chained = _engine.ModelOf(based.SyntaxTree).GetSymbolInfo(based).Symbol as IMethodSymbol;
                    code.Add(based.ArgumentList);
                }
                chained ??= ImplicitBase(type);
            }
            if (!toThis)
            {
                foreach (var (member, init) in Initializers(type))
                {
                    if (IsHeapField(member))
                    {
                        d.AddSelfWrite(Key(member));
                    }
                    code.Add(init.Value);
                }
            }
            if (chained != null)
            {
                d.Chained = Normal(chained);
                AddCallee(d, chained);
            }
            return code;
        }

        /// <summary>
        /// What code does, read off it: the fields it reads and writes, and everything it calls, written as a call or
        /// not (an accessor, an operator, a conversion, Deconstruct, an enumerator's members, Dispose, ToString).
        /// </summary>
        private void Walk(Direct d, IMethodSymbol m, List<SyntaxNode> bodies)
        {
            bool ctor = IsInstanceConstructor(m);
            SemanticModel Model(SyntaxNode n) => _engine.ModelOf(n.SyntaxTree);
            // (its body, and the lambdas and methods it hands a library member: the member runs them, so what they
            // do, it does; the member itself is judged by what each call hands it)
            var handed = new Dictionary<InvocationExpressionSyntax, IInvocationOperation>();
            for (int k = 0; k < bodies.Count; k++)
            {
                foreach (var inv in Within(bodies[k]).Prepend(bodies[k]).OfType<InvocationExpressionSyntax>())
                {
                    if (Model(inv).GetOperation(inv) is IInvocationOperation op && DelegatesHanded(op) is List<IOperation> delegates)
                    {
                        handed[inv] = op;
                        foreach (var made in delegates)
                        {
                            if (MethodHanded(made) is IMethodSymbol method)
                            {
                                AddCallee(d, method);
                            }
                            else
                            {
                                bodies.Add(made.Syntax);
                            }
                        }
                    }
                }
            }
            foreach (var node in bodies.SelectMany(b => Within(b).Prepend(b)))
            {
                var model = Model(node);
                switch (node)
                {
                    case SimpleNameSyntax name when model.GetSymbolInfo(name).Symbol is ISymbol s && IsHeapField(s):
                    {
                        // the whole access (o.F or F) and whether it is assigned
                        ExpressionSyntax access = name.Parent is MemberAccessExpressionSyntax ma && ma.Name == name ? ma : (ExpressionSyntax)name;
                        var (read, write) = Usage(access);
                        var key = Key(s);
                        if (read)
                        {
                            d.AddRead(key);
                        }
                        // (reading an atomic field moves what the reader knows of it on, past the others' steps)
                        if (write || read && Atomics.IsAtomic(s))
                        {
                            bool onThis = !s.IsStatic && (access is SimpleNameSyntax || access is MemberAccessExpressionSyntax mt && mt.Expression is ThisExpressionSyntax);
                            if (ctor && onThis)
                            {
                                d.AddSelfWrite(key);
                            } else
                            {
                                d.AddWrite(key);
                            }
                        }
                        break;
                    }
                    // a property or an indexer with accessors of its own (list.Count, list[i], a computed one): they run
                    case ExpressionSyntax pe when (pe is SimpleNameSyntax || pe is ElementAccessExpressionSyntax) &&
                                                  model.GetSymbolInfo(pe).Symbol is IPropertySymbol sp:
                    {
                        ExpressionSyntax access = pe.Parent is MemberAccessExpressionSyntax pm && pm.Name == pe ? pm : pe;
                        var (read, write) = Usage(access);
                        bool library = sp.OriginalDefinition.DeclaringSyntaxReferences.Length == 0;
                        if (read && sp.GetMethod != null && (library ? _engine.HasStub(sp.GetMethod) : true))
                        {
                            AddCallee(d, sp.GetMethod);
                        }
                        if (write && sp.SetMethod != null)
                        {
                            AddCallee(d, sp.SetMethod);
                        }
                        break;
                    }
                    case InvocationExpressionSyntax inv when model.GetSymbolInfo(inv).Symbol is IMethodSymbol callee:
                        if (SpecSymbols.IsModel(callee.ReducedFrom ?? callee.OriginalDefinition))
                        {
                            d.AddRead((callee.ReducedFrom ?? callee).OriginalDefinition);
                        }
                        else if (handed.TryGetValue(inv, out var op))
                        {
                            // (and what else the member is handed may run, as at any library call)
                            var lc = _engine.ContractOf(callee.OriginalDefinition);
                            d.All |= RunsOtherCodeAt(op, v => true) && !lc.IsPure;
                            LibraryModels(d, Normal(callee), lc);
                        }
                        else if (!SpecSymbols.IsSpecClass(callee.ContainingType))
                        {
                            AddCallee(d, callee);
                        }
                        break;
                    case BaseObjectCreationExpressionSyntax oc when model.GetSymbolInfo(oc).Symbol is IMethodSymbol ctorCallee:
                        AddCallee(d, ctorCallee);
                        break;
                    // (the calls nobody wrote as calls)
                    case CommonForEachStatementSyntax fe:
                    {
                        var info = model.GetForEachStatementInfo(fe);
                        foreach (var run in new[] { info.GetEnumeratorMethod, info.MoveNextMethod, info.CurrentProperty?.GetMethod, info.DisposeMethod })
                        {
                            AddOwn(d, run);
                        }
                        if (fe is ForEachVariableStatementSyntax fv)
                        {
                            AddDeconstruct(d, model.GetDeconstructionInfo(fv));
                        }
                        break;
                    }
                    case AssignmentExpressionSyntax da when da.Left is TupleExpressionSyntax || da.Left is DeclarationExpressionSyntax:
                        AddDeconstruct(d, model.GetDeconstructionInfo(da));
                        break;
                    case UsingStatementSyntax us:
                        AddDispose(d, us.Expression != null ? model.GetTypeInfo(us.Expression).Type : us.Declaration != null ? model.GetTypeInfo(us.Declaration.Type).Type : null);
                        break;
                    case LocalDeclarationStatementSyntax ud when !ud.UsingKeyword.IsKind(SyntaxKind.None):
                        AddDispose(d, model.GetTypeInfo(ud.Declaration.Type).Type);
                        break;
                    case PositionalPatternClauseSyntax pp:
                        AddOwn(d, model.GetSymbolInfo(pp).Symbol as IMethodSymbol);
                        break;
                    case InterpolationSyntax hole:
                        AddToString(d, model.GetOperation(hole.Expression));
                        break;
                }
                if (node is ExpressionSyntax e && model.GetOperation(e) is IOperation eo)
                {
                    Implied(d, eo);
                    // (the conversions around it, and the calls an initializer's element stands for: operations without syntax of their own)
                    for (var up = eo.Parent; up != null && up.IsImplicit && up.Syntax == e; up = up.Parent)
                    {
                        Implied(d, up);
                    }
                }
            }
        }

        /// <summary>The call an operation stands for, where it is one nobody wrote as a call.</summary>
        private void Implied(Direct d, IOperation op)
        {
            switch (op)
            {
                case IBinaryOperation b:
                    AddOwn(d, b.OperatorMethod);
                    // (a string made of an object: its ToString)
                    if (b.OperatorKind == BinaryOperatorKind.Add && b.Type?.SpecialType == SpecialType.System_String &&
                        (b.OperatorMethod == null || b.OperatorMethod.ContainingType.SpecialType == SpecialType.System_String))
                    {
                        AddToString(d, b.LeftOperand);
                        AddToString(d, b.RightOperand);
                    }
                    break;
                case IUnaryOperation u:
                    AddOwn(d, u.OperatorMethod);
                    break;
                case ICompoundAssignmentOperation ca:
                    AddOwn(d, ca.OperatorMethod);
                    break;
                case IIncrementOrDecrementOperation id:
                    AddOwn(d, id.OperatorMethod);
                    break;
                case IConversionOperation cv:
                    AddOwn(d, cv.OperatorMethod);
                    break;
                case IEventAssignmentOperation ea when ea.EventReference is IEventReferenceOperation er:
                    AddOwn(d, ea.Adds ? er.Event.AddMethod : er.Event.RemoveMethod);
                    break;
                // (an element of a collection's initializer: its Add)
                case IInvocationOperation { IsImplicit: true } inv:
                    if (inv.Parent is IObjectOrCollectionInitializerOperation)
                    {
                        AddCallee(d, inv.TargetMethod);
                    }
                    else
                    {
                        AddOwn(d, inv.TargetMethod);
                    }
                    break;
                case IObjectCreationOperation { IsImplicit: true, Constructor: { } made }:
                    AddCallee(d, made);
                    break;
            }
        }

        /// <summary>A member of the program's that code runs without naming it (a library's changes nothing of the program's by itself).</summary>
        private void AddOwn(Direct d, IMethodSymbol run)
        {
            if (run != null && !run.IsImplicitlyDeclared && (run.ReducedFrom ?? run).OriginalDefinition.DeclaringSyntaxReferences.Length > 0)
            {
                AddCallee(d, run);
            }
        }

        private void AddDeconstruct(Direct d, DeconstructionInfo info)
        {
            AddOwn(d, info.Method);
            foreach (var nested in info.Nested)
            {
                AddDeconstruct(d, nested);
            }
        }

        /// <summary>Leaving a using: the Dispose of what it holds (an object that may be of any class: any).</summary>
        private void AddDispose(Direct d, ITypeSymbol held)
        {
            if (held == null)
            {
                return;
            }
            for (var b = held; b != null; b = b.BaseType)
            {
                if (b.GetMembers("Dispose").Concat(b.GetMembers("DisposeAsync")).OfType<IMethodSymbol>()
                        .FirstOrDefault(x => x.Parameters.Length == 0 && x.DeclaringSyntaxReferences.Length > 0) is IMethodSymbol own)
                {
                    AddCallee(d, own);
                    return;
                }
            }
            d.All |= HandsOver(held);
        }

        /// <summary>May making a string of a value of this type (its ToString) change something of the program's?</summary>
        public bool StringOfWrites(ITypeSymbol t) => t != null && t.SpecialType != SpecialType.System_String && HandsOver(t);

        /// <summary>A value made a string: its ToString, the program's where its class has one, else whatever its object's class has.</summary>
        private void AddToString(Direct d, IOperation value)
        {
            if (value == null)
            {
                return;
            }
            while (value is IConversionOperation { IsImplicit: true } boxed)
            {
                value = boxed.Operand;
            }
            var t = value.Type;
            if (t == null || t.SpecialType == SpecialType.System_String)
            {
                return;
            }
            for (var b = t; b != null; b = b.BaseType)
            {
                if (b.GetMembers("ToString").OfType<IMethodSymbol>().FirstOrDefault(x => x.Parameters.Length == 0 && !x.IsImplicitlyDeclared && x.DeclaringSyntaxReferences.Length > 0) is IMethodSymbol own)
                {
                    AddCallee(d, own);
                    return;
                }
            }
            d.All |= HandsOver(t);
        }

        /// <summary>A body's nodes, but a lambda's or an anonymous method's inside it.</summary>
        private static IEnumerable<SyntaxNode> Within(SyntaxNode body) => body.DescendantNodes(n => n == body || !(n is AnonymousFunctionExpressionSyntax));

        /// <summary>
        /// The delegates a call hands a library member that is judged by what this call hands it: one no class
        /// overrides, every delegate it is handed a lambda or a method's (else null).
        /// </summary>
        private static List<IOperation> DelegatesHanded(IInvocationOperation call)
        {
            var m = call.TargetMethod;
            // (a specification's call is no code)
            if (m.OriginalDefinition.DeclaringSyntaxReferences.Length > 0 || m.MethodKind == MethodKind.DelegateInvoke || Engine.IsOverridable(m) ||
                SpecSymbols.IsSpecClass(m.ContainingType) || SpecSymbols.IsModel(m.ReducedFrom ?? m.OriginalDefinition))
            {
                return null;
            }
            var delegates = call.Arguments.Where(a => a.Parameter?.Type.TypeKind == TypeKind.Delegate).Select(a => a.Value).ToList();
            return delegates.All(x => x.Syntax is AnonymousFunctionExpressionSyntax || MethodHanded(x) != null) ? delegates : null;
        }

        /// <summary>The method a delegate is made of, where it is one's (xs.Select(Parse)).</summary>
        private static IMethodSymbol MethodHanded(IOperation value)
        {
            while (value is IConversionOperation c && c.IsImplicit)
            {
                value = c.Operand;
            }
            return value is IDelegateCreationOperation { Target: IMethodReferenceOperation reference } ? reference.Method : null;
        }

        /// <summary>
        /// A LINQ query made where it is handed over (xs.Where(f) in xs.Where(f).ToList()): enumerating it runs what
        /// its own call was handed, which is judged there.
        /// </summary>
        private static bool MadeHere(IOperation value)
        {
            while (value is IConversionOperation c && c.IsImplicit)
            {
                value = c.Operand;
            }
            return value is IInvocationOperation q && q.TargetMethod.ContainingType?.ToDisplayString() == "System.Linq.Enumerable";
        }

        /// <summary>Model state a library member changes or reads: what its stub says (Spec.Modifies, or nothing); without one, anything it reaches.</summary>
        private void LibraryModels(Direct d, IMethodSymbol m, Contract c)
        {
            if (!c.IsStub && MayTouchModels(m))
            {
                d.AddWrites(MutableModels());
            }
            if (c.IsStub && (c.Modifies != null || m.MethodKind == MethodKind.Constructor))
            {
                d.AddWrites(ModelsOf(m.ContainingType));
            }
            if (c.IsStub)
            {
                AddModelReads(d, c);
            }
        }

        /// <summary>The [Model] functions a stub's contract reads: a [Pure] stubbed member's value depends on them.</summary>
        private void AddModelReads(Direct d, Contract stub)
        {
            foreach (var inv in stub.Declaration.DescendantNodes().OfType<InvocationExpressionSyntax>())
            {
                if (stub.Model.GetSymbolInfo(inv).Symbol is IMethodSymbol callee)
                {
                    var key = (callee.ReducedFrom ?? callee).OriginalDefinition;
                    if (SpecSymbols.IsModel(key))
                    {
                        d.AddRead(key);
                    }
                    else if (!SpecSymbols.IsSpecClass(callee.ContainingType) && !SpecSymbols.IsSeqType(callee.ContainingType))
                    {
                        AddCallee(d, callee);
                    }
                }
            }
            // (and the stubbed members its contract names: list.Count)
            foreach (var name in stub.Declaration.DescendantNodes().OfType<SimpleNameSyntax>())
            {
                if (stub.Model.GetSymbolInfo(name).Symbol is IPropertySymbol p && p.GetMethod != null && _engine.HasStub(p.GetMethod))
                {
                    AddCallee(d, p.GetMethod);
                }
            }
        }

        /// <summary>The source methods that override or implement <paramref name="m"/>.</summary>
        internal IEnumerable<IMethodSymbol> Overrides(IMethodSymbol m)
        {
            // all levels: the overrides of the overrides too
            var found = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
            var work = new Stack<IMethodSymbol>();
            work.Push(m.OriginalDefinition);
            var all = _engine.SourceTypes.SelectMany(t => t.GetMembers().OfType<IMethodSymbol>()).ToList();
            while (work.Count > 0)
            {
                var b = work.Pop();
                foreach (var o in all)
                {
                    if (!SymbolEqualityComparer.Default.Equals(o, b) && _engine.BaseMembers(o).Contains(b, SymbolEqualityComparer.Default) && found.Add(o.OriginalDefinition))
                    {
                        work.Push(o.OriginalDefinition);
                    }
                }
            }
            return found;
        }

        /// <summary>
        /// May a call of this library method run user code: is it handed (as an argument, its receiver, or a type
        /// argument) a value through which it can (a delegate's Invoke, a key's Equals)?
        /// </summary>
        public bool RunsUserCode(IMethodSymbol m) =>
            m.Parameters.Any(p => HandsOver(p.Type)) ||
            (!m.IsStatic && HandsOver(m.ContainingType) && !(m.MethodKind == MethodKind.Constructor && (m.ContainingType.SpecialType == SpecialType.System_Object || m.ContainingType.IsGenericType && m.ContainingType.DeclaringSyntaxReferences.Length == 0))) ||
            // (making an empty collection of records calls none of their methods; what it's given to fill it, above, may)
            (m.MethodKind != MethodKind.Constructor || m.Parameters.Length > 0 && !m.Parameters.All(p => p.Type.SpecialType != SpecialType.None)) && m.ContainingType.TypeArguments.Concat(m.TypeArguments).Any(HandsOver);

        /// <summary>May a library member run code of its elements' or keys' types (their Equals, their CompareTo) that changes something?</summary>
        public bool ElementsRun(IMethodSymbol m) => m.ContainingType.TypeArguments.Concat(m.TypeArguments).Any(HandsOver);

        /// <summary>
        /// At this call, may the library method change the program's fields or model state? As
        /// <see cref="WritesOf"/> says for the method, but by what is actually handed to it: an <c>object</c> parameter
        /// given a program object whose class (and its subclasses) overrides nothing and implements no interface leaves
        /// the library nothing of the program's to run, no way to write its fields (reflection is not covered), and no
        /// list or dictionary to reach.
        /// </summary>
        public bool WritesFieldsAt(IInvocationOperation inv)
        {
            var m = inv.TargetMethod;
            if ((m.MethodKind != MethodKind.Constructor || m.Parameters.Length > 0 && !m.Parameters.All(p => p.Type.SpecialType != SpecialType.None)) &&
                m.ContainingType.TypeArguments.Concat(m.TypeArguments).Any(t => HandsOver(t) || ReachesModels(t)))
            {
                return true;
            }
            if (!m.IsStatic && m.MethodKind != MethodKind.Constructor && May(m.ContainingType, inv.Instance))
            {
                return true;
            }
            return inv.Arguments.Any(a => a.Parameter != null && May(a.Parameter.Type, a.ArgumentKind == ArgumentKind.Explicit ? a.Value : null));
        }

        private bool May(ITypeSymbol declared, IOperation value) =>
            (HandsOver(declared) || ReachesModels(declared)) && !(value?.ConstantValue.HasValue == true && value.ConstantValue.Value == null) &&
            (value == null || HandsOver(Handed(value)) || ReachesModels(Handed(value)));

        /// <summary>
        /// At this call of a library member that changes nothing it is given itself, might it run program code other
        /// than its delegate arguments that <paramref name="delegateOk"/> clears? Through its type arguments, its
        /// receiver, or an argument (an object whose class overrides Equals or implements IComparable), as above.
        /// </summary>
        public bool RunsOtherCodeAt(IInvocationOperation inv, System.Func<IOperation, bool> delegateOk)
        {
            var m = inv.TargetMethod;
            if (m.ContainingType.TypeArguments.Concat(m.TypeArguments).Any(HandsOver))
            {
                return true;
            }
            if (!m.IsStatic && inv.Instance != null && HandsOver(Handed(inv.Instance)))
            {
                return true;
            }
            foreach (var a in inv.Arguments)
            {
                if (a.Parameter == null)
                {
                    return true;
                }
                if (a.Parameter.Type.TypeKind == TypeKind.Delegate)
                {
                    if (!delegateOk(a.Value))
                    {
                        return true;
                    }
                    continue;
                }
                if (MadeHere(a.Value))
                {
                    continue;
                }
                if (a.ArgumentKind != ArgumentKind.Explicit ? HandsOver(a.Parameter.Type) : HandsOver(Handed(a.Value)))
                {
                    return true;
                }
            }
            return false;
        }

        /// <summary>The type of what is handed over: under implicit reference conversions (to object, to a base class).</summary>
        private static ITypeSymbol Handed(IOperation op)
        {
            while (op is IConversionOperation c && c.IsImplicit && c.Conversion.IsReference && c.Operand.Type != null)
            {
                op = c.Operand;
            }
            // a program class's object: only its class and subclasses can be there; a library type or interface: anything
            return op.Type is INamedTypeSymbol t && t.TypeKind == TypeKind.Class && t.DeclaringSyntaxReferences.Length > 0 ? t : op.Type;
        }

        /// <summary>
        /// Can a library method run user code through a value of this type: a delegate, an object of unknown class, or
        /// an object of a source class that overrides something (Equals, GetHashCode, ToString) or implements an
        /// interface (IComparable), or of a library class that a source class derives from?
        /// </summary>
        internal bool HandsOver(ITypeSymbol t)
        {
            switch (t)
            {
                case null: return false;
                case IArrayTypeSymbol a: return HandsOver(a.ElementType);
                case ITypeParameterSymbol _: return true;
            }
            // (a list interface: a library's collection, trusted to run nothing of the program's but its elements'
            // code; or an object of a class of the program's that implements it)
            if (t is INamedTypeSymbol { TypeKind: TypeKind.Interface, Arity: 1 } list && list.ContainingNamespace?.ToDisplayString() == "System.Collections.Generic" &&
                list.Name is "IList" or "IReadOnlyList" or "ICollection" or "IReadOnlyCollection" or "IReadOnlySet" or "ISet")
            {
                return HandsOver(list.TypeArguments[0]) ||
                       _engine.SourceTypes.Any(s => s.AllInterfaces.Any(i => SymbolEqualityComparer.Default.Equals(i.OriginalDefinition, list.OriginalDefinition)) && RunsUserCode(s));
            }
            // (a dictionary read through its interface: a library's, trusted likewise; or the program's own)
            if (Boogie.KernelTypes.IsReadOnlyDictionary(t))
            {
                var map = (INamedTypeSymbol)t;
                return map.TypeArguments.Any(HandsOver) ||
                       _engine.SourceTypes.Any(s => s.AllInterfaces.Any(i => SymbolEqualityComparer.Default.Equals(i.OriginalDefinition, map.OriginalDefinition)) && RunsUserCode(s));
            }
            if (t.TypeKind == TypeKind.Delegate || t.TypeKind == TypeKind.Interface || t.SpecialType == SpecialType.System_Object)
            {
                return true;
            }
            if (t.TypeKind != TypeKind.Class)
            {
                return t is INamedTypeSymbol v && v.TypeArguments.Any(HandsOver); // a struct holding them
            } // a struct holding them
            return _engine.SourceTypes.Any(s => DataTypes.Derives(s, t) && RunsUserCode(s)) || ((INamedTypeSymbol)t).TypeArguments.Any(HandsOver);
        }

        /// <summary>
        /// Code a library could run on an object of this source class, that may change something: an override, or an
        /// interface it implements.
        /// </summary>
        private bool RunsUserCode(INamedTypeSymbol s) =>
            (s.AllInterfaces.Length > 0 || s.GetMembers().Any(m => m.IsOverride) || s.IsRecord ||
             s.BaseType != null && s.BaseType.SpecialType != SpecialType.System_Object && s.BaseType.DeclaringSyntaxReferences.Length == 0) && !ChangesNothing(s);

        private readonly Dictionary<INamedTypeSymbol, bool> _changesNothing = new Dictionary<INamedTypeSymbol, bool>(SymbolEqualityComparer.Default);

        /// <summary>
        /// Does the code a library could run on an object of this source class change nothing? Its overrides and its
        /// interfaces' implementations write no field, model or array cell and read no cell, by these analyses; a
        /// record's own members compare, hash and print its fields, so those hand nothing over either.
        /// </summary>
        private bool ChangesNothing(INamedTypeSymbol s)
        {
            if (_changesNothing.TryGetValue(s, out var known))
            {
                return known;
            }
            // (while it is judged, a class that reaches itself isn't known to)
            _changesNothing[s] = false;
            return _changesNothing[s] = Judge();

            bool Judge()
            {
                var run = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
                for (var b = s; b != null && b.SpecialType != SpecialType.System_Object; b = b.BaseType)
                {
                    // (a library's class: its own code calls what the program overrides)
                    if (b.DeclaringSyntaxReferences.Length == 0 ||
                        b.IsRecord && b.GetMembers().OfType<IFieldSymbol>().Any(f => !f.IsStatic && HandsOver(f.Type)))
                    {
                        return false;
                    }
                    run.UnionWith(b.GetMembers().Where(m => m.IsOverride));
                }
                run.UnionWith(s.AllInterfaces.SelectMany(i => i.GetMembers()).Select(s.FindImplementationForInterfaceMember));
                foreach (var member in run)
                {
                    foreach (var m in member switch
                    {
                        IMethodSymbol method => new[] { method },
                        IPropertySymbol { SetMethod: null } p => new[] { p.GetMethod },
                        // (a setter writes; an event's accessors, or an implementation not found: not known)
                        _ => new IMethodSymbol[] { null },
                    })
                    {
                        if (m == null || m.MethodKind == MethodKind.PropertySet)
                        {
                            return false;
                        }
                        // (a record's own: its fields', above)
                        if (m.IsImplicitlyDeclared)
                        {
                            continue;
                        }
                        var (fields, all) = WritesOf(m);
                        if (all || fields.Count > 0 || _engine.MayWriteHeap(m) || _engine.MayTouchArrays(m))
                        {
                            return false;
                        }
                    }
                }
                return true;
            }
        }

        private void AddCallee(Direct d, IMethodSymbol callee)
        {
            d.AddCallee(Normal(callee));
        }

        /// <summary>Is the access read, written, or both (<c>o.F += 1</c>, <c>o.F++</c>, <c>ref o.F</c>)?</summary>
        private static (bool read, bool write) Usage(ExpressionSyntax access)
        {
            var e = access;
            while (e.Parent is ParenthesizedExpressionSyntax p)
            {
                e = p;
            }
            // (a part of a tuple that is assigned: (a, o.F) = ...)
            for (SyntaxNode part = e; part.Parent is ArgumentSyntax { Parent: TupleExpressionSyntax tuple }; part = tuple)
            {
                if (tuple.Parent is AssignmentExpressionSyntax ta && ta.Left == tuple || tuple.Parent is ForEachVariableStatementSyntax fv && fv.Variable == tuple)
                {
                    return (false, true);
                }
            }
            switch (e.Parent)
            {
                // (taken by reference: whoever holds the reference may write it)
                case RefExpressionSyntax:
                    return (true, true);
                case AssignmentExpressionSyntax a when a.Left == e:
                    return (!a.IsKind(SyntaxKind.SimpleAssignmentExpression), true);
                case PrefixUnaryExpressionSyntax pre when pre.IsKind(SyntaxKind.PreIncrementExpression) || pre.IsKind(SyntaxKind.PreDecrementExpression):
                    return (true, true);
                case PostfixUnaryExpressionSyntax post when post.IsKind(SyntaxKind.PostIncrementExpression) || post.IsKind(SyntaxKind.PostDecrementExpression):
                    return (true, true);
                case ArgumentSyntax arg when arg.RefKindKeyword.IsKind(SyntaxKind.RefKeyword) || arg.RefKindKeyword.IsKind(SyntaxKind.OutKeyword):
                    return (true, true);
                default:
                    return (true, false);
            }
        }

        /// <summary>The methods a call to <paramref name="m"/> may run (itself included).</summary>
        private List<IMethodSymbol> Reachable(IMethodSymbol m)
        {
            var seen = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
            var work = new Stack<IMethodSymbol>();
            work.Push(Normal(m));
            while (work.Count > 0)
            {
                var next = work.Pop();
                if (!seen.Add(next))
                {
                    continue;
                }
                foreach (var callee in DirectOf(next).Callees)
                {
                    work.Push(callee);
                }
            }
            return seen.ToList();
        }

        /// <summary>
        /// The heap fields a call may change, other than the fields of the object a constructor call builds:
        /// everything reachable writes (a reachable constructor's own self-writes are to an object built then).
        /// </summary>
        public (HashSet<ISymbol> fields, bool all) WritesOf(IMethodSymbol m)
        {
            var fields = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            bool all = false;
            foreach (var r in Reachable(m))
            {
                var d = DirectOf(r);
                fields.UnionWith(d.Writes);
                all |= d.All;
            }
            return (fields, all);
        }

        /// <summary>The fields a constructor sets on the object it builds: its own, and those of the constructors it runs on it first.</summary>
        public HashSet<ISymbol> SelfWritesOf(IMethodSymbol ctor)
        {
            var fields = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
            var seen = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
            for (var c = Normal(ctor); c != null && seen.Add(c); c = DirectOf(c).Chained)
            {
                fields.UnionWith(DirectOf(c).SelfWrites);
            }
            return fields;
        }

        /// <summary>
        /// An invariant is assumed of objects nobody re-checks, so it may depend only on state that cannot change
        /// behind its back: for a data record, nothing mutable at all (its positional fields never change); for an
        /// [Owned] class, only owned fields of <c>this</c>, which no one can write without this object's view.
        /// Returns why the invariant might depend on other state, or null.
        /// </summary>
        public string InvariantDependence(IMethodSymbol invariant, bool owned)
        {
            foreach (var m in Reachable(invariant))
            {
                var c = _engine.ContractOf(m);
                if (!c.HasSource)
                {
                    continue;
                }
                // array contents can be written by anyone holding the array (lengths never change)
                if (owned && c.Declaration.DescendantNodes().OfType<ElementAccessExpressionSyntax>()
                        .FirstOrDefault(e => c.Model.GetTypeInfo(e.Expression).Type is IArrayTypeSymbol) is ElementAccessExpressionSyntax element)
                {
                    return $"it reads '{element}', an array element, which anyone holding the array can change";
                }
                foreach (var name in c.Declaration.DescendantNodes().OfType<SimpleNameSyntax>())
                {
                    var s = c.Model.GetSymbolInfo(name).Symbol;
                    var access = name.Parent is MemberAccessExpressionSyntax ma && ma.Name == name ? ma : null;
                    bool onOther = m.IsStatic || access != null && !(access.Expression is ThisExpressionSyntax);
                    if (s != null && IsHeapField(s))
                    {
                        if (!owned)
                        {
                            return $"it reads '{access ?? (SyntaxNode)name}', a mutable field";
                        }
                        bool fixedField = s is IFieldSymbol rf && rf.IsReadOnly || s is IPropertySymbol rp && (rp.SetMethod == null || rp.SetMethod.IsInitOnly);
                        if (!SpecSymbols.IsOwned(s.ContainingType) && !fixedField)
                        {
                            return $"it reads '{access ?? (SyntaxNode)name}', which code without this object's view can change";
                        }
                        if (m.IsStatic)
                        {
                            return $"'{m.Name}' reads '{access ?? (SyntaxNode)name}' of whatever object it is given; read owned fields through this";
                        }
                        if (onOther && !OwnedChild(access.Expression, c.Model))
                        {
                            return $"it reads '{access ?? (SyntaxNode)name}' of another object, whose view someone else may hold";
                        }
                    }
                    else if (s is IMethodSymbol callee && !callee.IsStatic && access != null && !(access.Expression is ThisExpressionSyntax) &&
                             ReadsOf(callee).Count > 0)
                    {
                        return $"it calls '{access}', which reads the mutable state of another object";
                    }
                }
            }
            return null;
        }

        /// <summary>
        /// <c>F</c> or <c>this.F</c> for an [Owns] field F: an object this one owns. Its fields change only through
        /// Own.Take from this object, so this object's invariant may read them (one level down).
        /// </summary>
        private static bool OwnedChild(ExpressionSyntax e, SemanticModel model)
        {
            if (!(e is IdentifierNameSyntax || e is MemberAccessExpressionSyntax m && m.Expression is ThisExpressionSyntax))
            {
                return false;
            }
            return model.GetSymbolInfo(e).Symbol is ISymbol s && SpecSymbols.IsOwnsField(s);
        }

        /// <summary>
        /// Does a [Pure] function's value depend on array contents: does it (or anything it calls) read an element of
        /// an array, however it got the array (a parameter, a field)?
        /// </summary>
        /// <summary>
        /// Does every array element a [Pure] function (or anything it calls) reads come from its own array
        /// parameters? Then its value depends on those arrays' contents only, not on the whole array heap.
        /// </summary>
        public bool ReadsOnlyParameterArrays(IMethodSymbol m) =>
            Reachable(m).All(r => !(_engine.ContractOf(r) is Contract c && c.HasSource) ||
                c.Declaration.DescendantNodes().OfType<ElementAccessExpressionSyntax>()
                    .Where(e => StaticChecks.IsSequence(c.Model.GetTypeInfo(e.Expression).Type))
                    .All(e => c.Model.GetSymbolInfo(e.Expression).Symbol is IParameterSymbol p && SymbolEqualityComparer.Default.Equals(p.ContainingSymbol, r)));

        public bool ReadsArrays(IMethodSymbol m) =>
            Reachable(m).Any(r => _engine.ContractOf(r) is Contract c && c.HasSource &&
                (r.Parameters.Any(p => StaticChecks.IsSequence(p.Type)) ||
                 c.Declaration.DescendantNodes().OfType<ElementAccessExpressionSyntax>()
                     .Any(e => StaticChecks.IsSequence(c.Model.GetTypeInfo(e.Expression).Type))));

        /// <summary>The heap fields a [Pure] function's value may depend on (all it, or its callees, read), in a fixed order.</summary>
        public IReadOnlyList<ISymbol> ReadsOf(IMethodSymbol m) =>
            Reachable(m).SelectMany(r => DirectOf(r).Reads).Distinct(SymbolEqualityComparer.Default)
                .OrderBy(s => s.ToDisplayString()).ToList();
    }
}
