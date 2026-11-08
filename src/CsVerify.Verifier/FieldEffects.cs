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
            /// <summary>May write any heap field (a virtual call, a library call handed a callback or an object).</summary>
            public bool All;
        }

        private readonly Engine _engine;
        private readonly Dictionary<IMethodSymbol, Direct> _direct = new Dictionary<IMethodSymbol, Direct>(SymbolEqualityComparer.Default);

        public FieldEffects(Engine engine) { _engine = engine; }

        /// <summary>
        /// A member stored as mutable object state: an instance field or auto-property of a source class, or a mutable
        /// static field of one (the field of a single object, <see cref="IsStaticField"/>).
        /// </summary>
        public static bool IsHeapField(ISymbol s)
        {
            if (s == null || !(s.ContainingType is INamedTypeSymbol t) || t.TypeKind != TypeKind.Class) return false;
            if (t.ContainingNamespace?.ToDisplayString() == SpecSymbols.Namespace || s.DeclaringSyntaxReferences.Length == 0) return false;
            if (s.IsStatic) return s is IFieldSymbol sf && !sf.IsConst && !sf.IsReadOnly && !sf.IsImplicitlyDeclared;
            switch (s)
            {
                case IFieldSymbol f:
                    return !f.IsConst && !f.IsImplicitlyDeclared;
                case IPropertySymbol p:
                    if (p.IsIndexer || p.IsAbstract || p.IsVirtual || p.IsOverride) return false;
                    // an auto-property: accessors without bodies, declared as a property (positional ones are values)
                    return p.DeclaringSyntaxReferences.All(r => r.GetSyntax() is PropertyDeclarationSyntax pd && pd.AccessorList != null &&
                                                               pd.AccessorList.Accessors.All(a => a.Body == null && a.ExpressionBody == null));
                default:
                    return false;
            }
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
            .SelectMany(t => t.GetMembers()).Where(IsHeapField).Select(Key).Concat(_engine.Models).Distinct(SymbolEqualityComparer.Default).ToList();

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
            if (_engine.Models.Count == 0) return false;
            switch (t)
            {
                case null: return false;
                case IArrayTypeSymbol a: return ReachesModels(a.ElementType);
                case ITypeParameterSymbol _: return true;
            }
            if (t.SpecialType == SpecialType.System_String || t.SpecialType == SpecialType.System_Object || t.TypeKind == TypeKind.Interface || t.TypeKind == TypeKind.Delegate) return t.SpecialType != SpecialType.System_String;
            var modeled = _engine.Models.Select(x => (x.Parameters[0].Type as INamedTypeSymbol)?.OriginalDefinition).Where(x => x != null);
            if (modeled.Any(x => DataTypes.Derives(t, x) || DataTypes.Derives(x, t))) return true;
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
                foreach (var m in t.GetMembers())
                    if (!m.IsStatic && IsHeapField(m)) yield return Key(m);
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
            if (_direct.TryGetValue(m, out var d)) return d;
            _direct[m] = d = new Direct();
            // which body a virtual or interface call runs is not known statically: anything may be written
            if ((m.IsVirtual || m.IsAbstract || m.IsOverride || m.ContainingType?.TypeKind == TypeKind.Interface) &&
                !m.IsSealed && m.ContainingType?.IsSealed != true && !m.IsStatic)
                d.All = true;
            // a data value's constructor builds a value: it changes no state (its header's computed base arguments are pure)
            if (m.MethodKind == MethodKind.Constructor && _engine.Data.IsData(m.ContainingType)) return d;
            // a source class's implicit constructor only sets the new object's fields (defaults, initializers)
            if (m.IsImplicitlyDeclared && m.MethodKind == MethodKind.Constructor && m.ContainingType.DeclaringSyntaxReferences.Length > 0) return d;
            // a virtual member may run any override: they are all reachable from it
            if (Engine.IsOverridable(m))
                foreach (var o in Overrides(m)) d.Callees.Add(o);
            var c = _engine.ContractOf(m.OriginalDefinition);
            if (!c.HasSource || c.IsStub)
            {
                // a library method cannot name user fields; it can reach them only by running user code it is handed
                // (its receiver included: a delegate's Invoke)
                d.All = RunsUserCode(m) && !c.IsPure; // (a [Pure] stub says it has no effects: trusted, like all it says)
                // model state: a stub says what it changes (Spec.Modifies, or nothing); without one, anything it reaches
                if (!c.IsStub && MayTouchModels(m)) d.Writes.UnionWith(MutableModels());
                if (c.IsStub && (c.Modifies != null || m.MethodKind == MethodKind.Constructor)) d.Writes.UnionWith(ModelsOf(m.ContainingType));
                if (c.IsStub) AddModelReads(d, c);
                return d;
            }
            bool ctor = m.MethodKind == MethodKind.Constructor;
            foreach (var node in c.Declaration.DescendantNodes(n => !(n is AnonymousFunctionExpressionSyntax)))
            {
                switch (node)
                {
                    case SimpleNameSyntax name when c.Model.GetSymbolInfo(name).Symbol is ISymbol s && IsHeapField(s):
                    {
                        // the whole access (o.F or F) and whether it is assigned
                        ExpressionSyntax access = name.Parent is MemberAccessExpressionSyntax ma && ma.Name == name ? ma : (ExpressionSyntax)name;
                        var (read, write) = Usage(access);
                        var key = Key(s);
                        if (read) d.Reads.Add(key);
                        // (reading an atomic field moves what the reader knows of it on, past the others' steps)
                        if (write || read && Atomics.IsAtomic(s))
                        {
                            bool onThis = access is SimpleNameSyntax || access is MemberAccessExpressionSyntax mt && mt.Expression is ThisExpressionSyntax;
                            if (ctor && onThis) d.SelfWrites.Add(key); else d.Writes.Add(key);
                        }
                        break;
                    }
                    // a stubbed property or indexer (list.Count, list[i]): its accessors run
                    case ExpressionSyntax pe when (pe is SimpleNameSyntax || pe is ElementAccessExpressionSyntax) &&
                                                  c.Model.GetSymbolInfo(pe).Symbol is IPropertySymbol sp && sp.DeclaringSyntaxReferences.Length == 0:
                    {
                        ExpressionSyntax access = pe.Parent is MemberAccessExpressionSyntax pm && pm.Name == pe ? pm : pe;
                        var (read, write) = Usage(access);
                        if (read && sp.GetMethod != null && _engine.HasStub(sp.GetMethod)) AddCallee(d, sp.GetMethod);
                        if (write && sp.SetMethod != null) AddCallee(d, sp.SetMethod);
                        break;
                    }
                    case InvocationExpressionSyntax inv when c.Model.GetSymbolInfo(inv).Symbol is IMethodSymbol callee:
                        if (SpecSymbols.IsModel(callee.ReducedFrom ?? callee.OriginalDefinition)) d.Reads.Add((callee.ReducedFrom ?? callee).OriginalDefinition);
                        else if (!SpecSymbols.IsSpecClass(callee.ContainingType)) AddCallee(d, callee);
                        break;
                    case BaseObjectCreationExpressionSyntax oc when c.Model.GetSymbolInfo(oc).Symbol is IMethodSymbol ctorCallee:
                        AddCallee(d, ctorCallee);
                        break;
                    case ConstructorInitializerSyntax ci when c.Model.GetSymbolInfo(ci).Symbol is IMethodSymbol baseCtor:
                        AddCallee(d, baseCtor);
                        break;
                }
            }
            return d;
        }

        /// <summary>The [Model] functions a stub's contract reads: a [Pure] stubbed member's value depends on them.</summary>
        private void AddModelReads(Direct d, Contract stub)
        {
            foreach (var inv in stub.Declaration.DescendantNodes().OfType<InvocationExpressionSyntax>())
                if (stub.Model.GetSymbolInfo(inv).Symbol is IMethodSymbol callee)
                {
                    var key = (callee.ReducedFrom ?? callee).OriginalDefinition;
                    if (SpecSymbols.IsModel(key)) d.Reads.Add(key);
                    else if (!SpecSymbols.IsSpecClass(callee.ContainingType) && !SpecSymbols.IsSeqType(callee.ContainingType)) AddCallee(d, callee);
                }
            // (and the stubbed members its contract names: list.Count)
            foreach (var name in stub.Declaration.DescendantNodes().OfType<SimpleNameSyntax>())
                if (stub.Model.GetSymbolInfo(name).Symbol is IPropertySymbol p && p.GetMethod != null && _engine.HasStub(p.GetMethod))
                    AddCallee(d, p.GetMethod);
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
                    if (!SymbolEqualityComparer.Default.Equals(o, b) && _engine.BaseMembers(o).Contains(b, SymbolEqualityComparer.Default) && found.Add(o.OriginalDefinition))
                        work.Push(o.OriginalDefinition);
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
            bool May(ITypeSymbol declared, IOperation value) =>
                (HandsOver(declared) || ReachesModels(declared)) && !(value?.ConstantValue.HasValue == true && value.ConstantValue.Value == null) &&
                (value == null || HandsOver(Handed(value)) || ReachesModels(Handed(value)));
            if ((m.MethodKind != MethodKind.Constructor || m.Parameters.Length > 0 && !m.Parameters.All(p => p.Type.SpecialType != SpecialType.None)) &&
                m.ContainingType.TypeArguments.Concat(m.TypeArguments).Any(t => HandsOver(t) || ReachesModels(t))) return true;
            if (!m.IsStatic && m.MethodKind != MethodKind.Constructor && May(m.ContainingType, inv.Instance)) return true;
            return inv.Arguments.Any(a => a.Parameter != null && May(a.Parameter.Type, a.ArgumentKind == ArgumentKind.Explicit ? a.Value : null));
        }

        /// <summary>
        /// At this call of a library member that changes nothing it is given itself, might it run program code other
        /// than its delegate arguments that <paramref name="delegateOk"/> clears? Through its type arguments, its
        /// receiver, or an argument (an object whose class overrides Equals or implements IComparable), as above.
        /// </summary>
        public bool RunsOtherCodeAt(IInvocationOperation inv, System.Func<IOperation, bool> delegateOk)
        {
            var m = inv.TargetMethod;
            if (m.ContainingType.TypeArguments.Concat(m.TypeArguments).Any(HandsOver)) return true;
            if (!m.IsStatic && inv.Instance != null && HandsOver(Handed(inv.Instance))) return true;
            foreach (var a in inv.Arguments)
            {
                if (a.Parameter == null) return true;
                if (a.Parameter.Type.TypeKind == TypeKind.Delegate) { if (!delegateOk(a.Value)) return true; continue; }
                if (a.ArgumentKind != ArgumentKind.Explicit ? HandsOver(a.Parameter.Type) : HandsOver(Handed(a.Value))) return true;
            }
            return false;
        }

        /// <summary>The type of what is handed over: under implicit reference conversions (to object, to a base class).</summary>
        private static ITypeSymbol Handed(IOperation op)
        {
            while (op is IConversionOperation c && c.IsImplicit && c.Conversion.IsReference && c.Operand.Type != null) op = c.Operand;
            // a program class's object: only its class and subclasses can be there; a library type or interface: anything
            return op.Type is INamedTypeSymbol t && t.TypeKind == TypeKind.Class && t.DeclaringSyntaxReferences.Length > 0 ? t : op.Type;
        }

        /// <summary>
        /// Can a library method run user code through a value of this type: a delegate, an object of unknown class, or
        /// an object of a source class that overrides something (Equals, GetHashCode, ToString) or implements an
        /// interface (IComparable), or of a library class that a source class derives from?
        /// </summary>
        private bool HandsOver(ITypeSymbol t)
        {
            switch (t)
            {
                case null: return false;
                case IArrayTypeSymbol a: return HandsOver(a.ElementType);
                case ITypeParameterSymbol _: return true;
            }
            if (t.TypeKind == TypeKind.Delegate || t.TypeKind == TypeKind.Interface || t.SpecialType == SpecialType.System_Object) return true;
            if (t.TypeKind != TypeKind.Class) return t is INamedTypeSymbol v && v.TypeArguments.Any(HandsOver); // a struct holding them
            return _engine.SourceTypes.Any(s => DataTypes.Derives(s, t) && RunsUserCode(s)) || ((INamedTypeSymbol)t).TypeArguments.Any(HandsOver);
        }

        /// <summary>Code a library could run on an object of this source class: an override, or an interface it implements.</summary>
        private static bool RunsUserCode(INamedTypeSymbol s) =>
            s.AllInterfaces.Length > 0 || s.GetMembers().Any(m => m.IsOverride) || s.IsRecord ||
            s.BaseType != null && s.BaseType.SpecialType != SpecialType.System_Object && s.BaseType.DeclaringSyntaxReferences.Length == 0;

        private void AddCallee(Direct d, IMethodSymbol callee)
        {
            d.Callees.Add(Normal(callee));
        }

        /// <summary>Is the access read, written, or both (<c>o.F += 1</c>, <c>o.F++</c>, <c>ref o.F</c>)?</summary>
        private static (bool read, bool write) Usage(ExpressionSyntax access)
        {
            var e = access;
            while (e.Parent is ParenthesizedExpressionSyntax p) e = p;
            switch (e.Parent)
            {
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
                if (!seen.Add(next)) continue;
                foreach (var callee in DirectOf(next).Callees) work.Push(callee);
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

        /// <summary>The fields a constructor sets on the object it builds.</summary>
        public HashSet<ISymbol> SelfWritesOf(IMethodSymbol ctor) => DirectOf(ctor).SelfWrites;

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
                if (!c.HasSource) continue;
                // array contents can be written by anyone holding the array (lengths never change)
                if (owned && c.Declaration.DescendantNodes().OfType<ElementAccessExpressionSyntax>()
                        .FirstOrDefault(e => c.Model.GetTypeInfo(e.Expression).Type is IArrayTypeSymbol) is ElementAccessExpressionSyntax element)
                    return $"it reads '{element}', an array element, which anyone holding the array can change";
                foreach (var name in c.Declaration.DescendantNodes().OfType<SimpleNameSyntax>())
                {
                    var s = c.Model.GetSymbolInfo(name).Symbol;
                    var access = name.Parent is MemberAccessExpressionSyntax ma && ma.Name == name ? ma : null;
                    bool onOther = m.IsStatic || access != null && !(access.Expression is ThisExpressionSyntax);
                    if (s != null && IsHeapField(s))
                    {
                        if (!owned) return $"it reads '{access ?? (SyntaxNode)name}', a mutable field";
                        bool fixedField = s is IFieldSymbol rf && rf.IsReadOnly || s is IPropertySymbol rp && (rp.SetMethod == null || rp.SetMethod.IsInitOnly);
                        if (!SpecSymbols.IsOwned(s.ContainingType) && !fixedField) return $"it reads '{access ?? (SyntaxNode)name}', which code without this object's view can change";
                        if (m.IsStatic) return $"'{m.Name}' reads '{access ?? (SyntaxNode)name}' of whatever object it is given; read owned fields through this";
                        if (onOther && !OwnedChild(access.Expression, c.Model))
                            return $"it reads '{access ?? (SyntaxNode)name}' of another object, whose view someone else may hold";
                    }
                    else if (s is IMethodSymbol callee && !callee.IsStatic && access != null && !(access.Expression is ThisExpressionSyntax) &&
                             ReadsOf(callee).Count > 0)
                        return $"it calls '{access}', which reads the mutable state of another object";
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
            if (!(e is IdentifierNameSyntax || e is MemberAccessExpressionSyntax m && m.Expression is ThisExpressionSyntax)) return false;
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
                    .Where(e => MethodVerifier.IsSequence(c.Model.GetTypeInfo(e.Expression).Type))
                    .All(e => c.Model.GetSymbolInfo(e.Expression).Symbol is IParameterSymbol p && SymbolEqualityComparer.Default.Equals(p.ContainingSymbol, r)));

        public bool ReadsArrays(IMethodSymbol m) =>
            Reachable(m).Any(r => _engine.ContractOf(r) is Contract c && c.HasSource &&
                (r.Parameters.Any(p => MethodVerifier.IsSequence(p.Type)) ||
                 c.Declaration.DescendantNodes().OfType<ElementAccessExpressionSyntax>()
                     .Any(e => MethodVerifier.IsSequence(c.Model.GetTypeInfo(e.Expression).Type))));

        /// <summary>The heap fields a [Pure] function's value may depend on (all it, or its callees, read), in a fixed order.</summary>
        public IReadOnlyList<ISymbol> ReadsOf(IMethodSymbol m) =>
            Reachable(m).SelectMany(r => DirectOf(r).Reads).Distinct(SymbolEqualityComparer.Default)
                .OrderBy(s => s.ToDisplayString()).ToList();
    }
}
